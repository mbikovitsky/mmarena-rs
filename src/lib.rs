//! `mmap`-based arena allocator.

#![deny(missing_docs)]
#![cfg_attr(not(test), no_std)]

use core::{cell::Cell, ffi::c_void, mem::MaybeUninit, ptr::NonNull};

/// An arena of objects of type `T`.
///
/// The API is modeled after [`typed_arena`](https://docs.rs/typed-arena/latest/typed_arena/).
#[derive(Debug)]
pub struct Arena<T> {
    buffer: *mut T,
    len: Cell<usize>,
    committed: Cell<usize>,
    capacity: usize,
}

impl<T> Arena<T> {
    const ELEM_SIZE: usize = core::mem::size_of::<T>();
    const ELEM_ALIGN: usize = core::mem::align_of::<T>();

    /// Constructs a new arena with the given capacity.
    ///
    /// Enough virtual memory to hold `capacity` items is reserved here, but no
    /// physical memory or swap space is committed.
    ///
    /// Panics if the requested capacity cannot be reserved.
    pub fn new(capacity: usize) -> Self {
        if capacity == 0 {
            return Self {
                buffer: core::ptr::null_mut(),
                len: Cell::new(0),
                committed: Cell::new(0),
                capacity: 0,
            };
        }

        let buffer_size = Self::ELEM_SIZE
            .checked_mul(capacity)
            .expect("Total memory for the arena should fit in usize");

        let buffer: *mut T = reserve_virtual_memory(buffer_size).cast();
        assert!(!buffer.is_null(), "Failed reserving requested memory");

        assert_eq!((buffer as usize) % Self::ELEM_ALIGN, 0);

        Self {
            buffer,
            len: Cell::new(0),
            committed: Cell::new(0),
            capacity,
        }
    }

    /// Returns the number of elements currently in the arena.
    pub fn len(&self) -> usize {
        self.len.get()
    }

    /// Returns the capacity of the arena.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Allows mutable iteration over the arena elements.
    ///
    /// Items are returned in order of allocation.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        (0..self.len.get()).map(|i| unsafe { self.buffer.wrapping_add(i).as_mut().unwrap() })
    }

    /// Allocates a new element in the arena, and returns a mutable reference to it.
    pub fn alloc(&self, value: T) -> &mut T {
        unsafe {
            let elements = self.alloc_uninitialized(1);
            assert_eq!(elements.len(), 1);
            elements[0].write(value)
        }
    }

    /// Allocates elements in the arena from an iterator.
    /// Returns a mutable slice that contains the allocated elements.
    pub fn alloc_extend(&self, iterable: impl IntoIterator<Item = T>) -> &mut [T] {
        let mut iterator = iterable.into_iter();

        self.commit(iterator.size_hint().0);

        let first: *mut T = if let Some(value) = iterator.next() {
            self.alloc(value)
        } else {
            unsafe {
                return core::slice::from_raw_parts_mut(NonNull::dangling().as_ptr(), 0);
            }
        };

        let mut len: usize = 1;
        let mut size: isize = Self::ELEM_SIZE.try_into().unwrap();

        for elem in iterator {
            self.alloc(elem);
            len = len.checked_add(1).unwrap();
            size = size
                .checked_add(Self::ELEM_SIZE.try_into().unwrap())
                .unwrap();
        }

        unsafe { core::slice::from_raw_parts_mut(first, len) }
    }

    /// Allocates memory for `count` elements, but doesn't initialize it.
    ///
    /// # Safety
    ///
    /// After calling this method, the arena considers the elements initialized.
    /// Dropping the arena without actually initializing them is undefined behaviour.
    pub unsafe fn alloc_uninitialized(&self, count: usize) -> &mut [MaybeUninit<T>] {
        self.commit(count);
        let elements = &mut self.uninitialized_array().as_mut()[..count];
        self.len.set(self.len.get() + count);
        elements
    }

    /// Commits enough memory for at least `count` *more* elements.
    ///
    /// This can be used as an optimization, to avoid committing on subsequent `alloc_`
    /// calls.
    pub fn commit(&self, count: usize) {
        if count == 0 {
            return;
        }

        assert!(
            (count <= self.capacity) && (self.len.get() <= self.capacity - count),
            "Not enough memory"
        );

        assert!(!self.buffer.is_null());

        unsafe {
            if self.committed.get().checked_sub(self.len.get()).unwrap() < count {
                let committed = commit_virtual_memory(
                    self.buffer.wrapping_add(self.len.get()).cast(),
                    count * Self::ELEM_SIZE,
                );
                assert!(committed, "Failed committing memory for new elements");

                self.committed.set(self.len.get() + count);
            }
        }
    }

    /// Returns unused space.
    ///
    /// # Safety
    ///
    /// The returned elements are not considered allocated by the arena, so they won't
    /// be dropped unless there are further calls to `alloc_` methods.
    ///
    /// A raw pointer is returned to avoid creating multiple mutable references to
    /// the same place. Do not to dereference it after any of the `alloc_` methods
    /// are called.
    pub fn uninitialized_array(&self) -> NonNull<[MaybeUninit<T>]> {
        let uninitialized_len = self.committed.get().checked_sub(self.len.get()).unwrap();

        // Assert we don't violate slice limitations
        assert!(
            uninitialized_len * Self::ELEM_SIZE <= isize::MAX.try_into().unwrap(),
            "Uninitialized space too large to return"
        );

        let uninitialized_base: *mut MaybeUninit<T> = if uninitialized_len == 0 {
            // We need a non-null pointer, but self.buffer may be null
            NonNull::dangling().as_ptr()
        } else {
            self.buffer.wrapping_add(self.len.get()).cast()
        };

        assert!(!uninitialized_base.is_null());

        let ptr = core::ptr::slice_from_raw_parts_mut(uninitialized_base, uninitialized_len);
        NonNull::new(ptr).unwrap()
    }
}

impl Arena<u8> {
    /// Allocates a string slice and returns a mutable reference to it.
    pub fn alloc_str(&self, string: &str) -> &mut str {
        let buffer = self.alloc_extend(string.bytes());
        unsafe { core::str::from_utf8_unchecked_mut(buffer) }
    }
}

impl<T> Drop for Arena<T> {
    fn drop(&mut self) {
        unsafe {
            for i in 0..self.len.get() {
                core::ptr::drop_in_place(self.buffer.wrapping_add(i));
            }
            release_virtual_memory(self.buffer.cast(), self.capacity * Self::ELEM_SIZE)
        }
    }
}

#[cfg(windows)]
fn reserve_virtual_memory(size: usize) -> *mut c_void {
    use winapi::um::{
        memoryapi::VirtualAlloc,
        winnt::{MEM_RESERVE, PAGE_NOACCESS},
    };

    unsafe { VirtualAlloc(core::ptr::null_mut(), size, MEM_RESERVE, PAGE_NOACCESS).cast() }
}

#[cfg(unix)]
fn reserve_virtual_memory(size: usize) -> *mut c_void {
    unsafe {
        libc::mmap(
            core::ptr::null_mut(),
            size,
            libc::PROT_NONE,
            libc::MAP_PRIVATE | libc::MAP_ANON,
            -1,
            0,
        )
    }
}

#[cfg(windows)]
unsafe fn commit_virtual_memory(address: *mut c_void, size: usize) -> bool {
    use winapi::um::{
        memoryapi::VirtualAlloc,
        winnt::{MEM_COMMIT, PAGE_READWRITE},
    };

    unsafe { !VirtualAlloc(address.cast(), size, MEM_COMMIT, PAGE_READWRITE).is_null() }
}

#[cfg(unix)]
unsafe fn commit_virtual_memory(address: *mut c_void, size: usize) -> bool {
    let page_size = get_page_size();
    assert!(page_size.is_power_of_two());

    let base_address = ((address as usize) & (!(page_size - 1))) as *mut c_void;
    let size_to_commit = size + (address as usize - base_address as usize);

    unsafe {
        libc::mprotect(
            base_address,
            size_to_commit,
            libc::PROT_READ | libc::PROT_WRITE,
        ) == 0
    }
}

#[cfg(windows)]
unsafe fn release_virtual_memory(address: *mut c_void, _size: usize) {
    use winapi::um::{memoryapi::VirtualFree, winnt::MEM_RELEASE};

    unsafe {
        VirtualFree(address.cast(), 0, MEM_RELEASE);
    }
}

#[cfg(unix)]
unsafe fn release_virtual_memory(address: *mut c_void, size: usize) {
    unsafe {
        libc::munmap(address, size);
    }
}

#[cfg(windows)]
#[allow(dead_code)]
fn get_page_size() -> usize {
    use winapi::um::sysinfoapi::GetSystemInfo;

    let mut system_info = unsafe { core::mem::zeroed() };
    unsafe { GetSystemInfo(&mut system_info) };

    system_info.dwPageSize.try_into().unwrap()
}

#[cfg(unix)]
fn get_page_size() -> usize {
    unsafe { libc::sysconf(libc::_SC_PAGESIZE).try_into().unwrap() }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::panic::{self, AssertUnwindSafe};

    use crate::{get_page_size, Arena};

    struct DropTracker<'a> {
        drops: &'a Cell<usize>,
    }

    impl<'a> Drop for DropTracker<'a> {
        fn drop(&mut self) {
            self.drops.set(self.drops.get() + 1);
        }
    }

    #[test]
    fn new_and_drop() {
        Arena::<u8>::new(0x1000);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn new_huge() {
        // Reserve 1TB
        Arena::<u8>::new(1 << 40);
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn new_huge() {
        // Reserve 1GB
        Arena::<u8>::new(1 << 30);
    }

    #[test]
    fn alloc() {
        let capacity = 0x1000;

        let drops = Cell::new(0);

        let arena = Arena::new(capacity);

        for _ in 0..capacity {
            arena.alloc(DropTracker { drops: &drops });
        }

        drop(arena);

        assert_eq!(drops.get(), capacity);
    }

    #[test]
    fn alloc_past_end() {
        let arena = Arena::new(1);

        arena.alloc(1);

        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            arena.alloc(2);
        }));
        assert!(result.is_err());
    }

    #[test]
    fn zero_sized_arena() {
        Arena::<u8>::new(0);
    }

    #[test]
    fn zero_sized_arena_cant_allocate() {
        let arena = Arena::new(0);

        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            arena.alloc(1);
        }));
        assert!(result.is_err());
    }

    #[test]
    fn alloc_more_than_page_size() {
        const MORE_THAN_PAGE_SIZE: usize = 10 * 1024 * 1024; // 10MB
        assert!(MORE_THAN_PAGE_SIZE > get_page_size());

        let arena: Arena<u8> = Arena::new(MORE_THAN_PAGE_SIZE);

        let blob = arena.alloc_extend((0..MORE_THAN_PAGE_SIZE).map(|i| i as u8));

        assert!(blob
            .iter()
            .enumerate()
            .all(|(index, &element)| index as u8 == element));
    }

    #[test]
    fn alloc_str() {
        static STRING: &str = "Hello, world!";

        let arena = Arena::new(STRING.len());

        let arena_string = arena.alloc_str(STRING);

        assert_eq!(arena_string, STRING);
    }

    #[test]
    fn uninitialized_array() {
        let arena = Arena::<u8>::new(10);

        assert_eq!(arena.uninitialized_array().len(), 0);

        arena.commit(5);
        assert_eq!(arena.uninitialized_array().len(), 5);

        arena.commit(5);
        assert_eq!(arena.uninitialized_array().len(), 5);

        arena.commit(10);
        assert_eq!(arena.uninitialized_array().len(), 10);

        arena.alloc_extend((0..10).map(|_| 42));
        assert_eq!(arena.uninitialized_array().len(), 0);
    }
}
