//! AtomicPtr with stamp to avoid [ABA problem](https://en.wikipedia.org/wiki/ABA_problem)
//!
//! ## Examples
//! ```
//! use atomic_stamped_ptr::{AtomicStampedPtr, StampedPtr, Ordering};
//! let some_ptr  = AtomicStampedPtr::new(&mut 5);
//! let other_ptr = &mut 10;
//! let old_stamped_ptr = some_ptr.load(Ordering::Relaxed);
//! some_ptr.store(old_stamped_ptr.successor(other_ptr), Ordering::Relaxed);
//! // or
//! some_ptr.store(StampedPtr::new(other_ptr), Ordering::Relaxed);
//! ```
#![no_std]
use atomic::Atomic;
use core::ptr::null_mut;
#[allow(unused_imports)]
use core::sync::atomic::Ordering::*;

pub use core::sync::atomic::Ordering;

#[derive(Default)]
pub struct AtomicStampedPtr<T> {
    p: Atomic<StampedPtr<T>>,
}

impl<T> AtomicStampedPtr<T> {
    /// Creates a new [`AtomicStampedPtr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::AtomicStampedPtr;
    ///
    /// let atomic_stamped_ptr = AtomicStampedPtr::new(&mut 5);
    /// ```
    #[inline]
    pub const fn new(ptr: *mut T) -> Self {
        Self {
            p: Atomic::new(StampedPtr::new(ptr)),
        }
    }

    /// Returns a mutable reference to the underlying pointer.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::{AtomicStampedPtr, Ordering};
    ///
    /// let mut atomic_stamped_ptr = AtomicStampedPtr::new(&mut 10);
    /// atomic_stamped_ptr.get_mut().ptr = &mut 5;
    /// assert_eq!(unsafe { *atomic_stamped_ptr.load(Ordering::SeqCst).ptr }, 5);
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut StampedPtr<T> {
        self.p.get_mut()
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::AtomicStampedPtr;
    ///
    /// let atomic_stamped_ptr = AtomicStampedPtr::new(&mut 5);
    /// assert_eq!(unsafe { *atomic_stamped_ptr.into_inner() }, 5);
    /// ```
    #[inline]
    pub fn into_inner(self) -> *mut T {
        self.p.into_inner().ptr
    }

    /// Loads a value from the pointer.
    ///
    /// `load` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`SeqCst`], [`Acquire`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`] or [`AcqRel`].
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::{AtomicStampedPtr, Ordering};
    ///
    /// let some_ptr  = AtomicStampedPtr::new(&mut 5);
    ///
    /// let value = some_ptr.load(Ordering::Relaxed);
    /// ```
    #[inline]
    pub fn load(&self, order: Ordering) -> StampedPtr<T> {
        self.p.load(order)
    }

    /// Stores a value with new version into the pointer.
    ///
    /// `store` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`SeqCst`], [`Release`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Acquire`] or [`AcqRel`].
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::{AtomicStampedPtr, StampedPtr, Ordering};
    ///
    /// let some_ptr  = AtomicStampedPtr::new(&mut 5);
    ///
    /// let other_ptr = &mut 10;
    ///
    /// let old_stamped_ptr = some_ptr.load(Ordering::Relaxed);
    /// some_ptr.store(old_stamped_ptr.successor(other_ptr), Ordering::Relaxed);
    /// // or
    /// some_ptr.store(StampedPtr::new(other_ptr), Ordering::Relaxed);
    /// ```
    #[inline]
    pub fn store(&self, ptr: StampedPtr<T>, order: Ordering) {
        self.p.store(ptr, order);
    }

    /// Stores a value into the pointer, returning the previous value.
    ///
    /// `swap` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. All ordering modes are possible. Note that using
    /// [`Acquire`] makes the store part of this operation [`Relaxed`], and
    /// using [`Release`] makes the load part [`Relaxed`].
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::{AtomicStampedPtr, StampedPtr, Ordering};
    ///
    /// let some_ptr  = AtomicStampedPtr::new(&mut 5);
    ///
    /// let other_ptr = &mut 10;
    ///
    /// let old_stamped_ptr = some_ptr.load(Ordering::Relaxed);
    /// let value = some_ptr.swap(old_stamped_ptr.successor(other_ptr), Ordering::Relaxed);
    /// // or
    /// let value = some_ptr.swap(StampedPtr::new(other_ptr), Ordering::Relaxed);
    /// ```
    #[inline]
    pub fn swap(&self, ptr: StampedPtr<T>, order: Ordering) -> StampedPtr<T> {
        self.p.swap(ptr, order)
    }

    /// Stores a value into the pointer if the current value is the same as the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and containing
    /// the previous value. On success this value is guaranteed to be equal to `current`.
    ///
    /// `compare_exchange` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::{AtomicStampedPtr, Ordering};
    ///
    /// let some_ptr = AtomicStampedPtr::new(&mut 5);
    ///
    /// let other_ptr = &mut 10;
    ///
    /// let old_stamped_ptr = some_ptr.load(Ordering::Relaxed);
    /// let value = some_ptr.compare_exchange(old_stamped_ptr, old_stamped_ptr.successor(other_ptr),
    ///                                       Ordering::SeqCst, Ordering::Relaxed);
    /// ```
    #[inline]
    pub fn compare_exchange(
        &self,
        current: StampedPtr<T>,
        new: StampedPtr<T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<StampedPtr<T>, StampedPtr<T>> {
        self.p.compare_exchange(current, new, success, failure)
    }

    /// Stores a value into the pointer if the current value is the same as the `current` value.
    ///
    /// Unlike [`AtomicStampedPtr::compare_exchange`], this function is allowed to spuriously fail even when the
    /// comparison succeeds, which can result in more efficient code on some platforms. The
    /// return value is a result indicating whether the new value was written and containing the
    /// previous value.
    ///
    /// `compare_exchange_weak` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_stamped_ptr::{AtomicStampedPtr, StampedPtr, Ordering};
    ///
    /// let some_ptr = AtomicStampedPtr::new(&mut 5);
    ///
    /// let mut old = some_ptr.load(Ordering::Relaxed);
    /// let new = old.successor(&mut 10);
    /// loop {
    ///     match some_ptr.compare_exchange_weak(old, new, Ordering::SeqCst, Ordering::Relaxed) {
    ///         Ok(_) => break,
    ///         Err(x) => old = x,
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn compare_exchange_weak(
        &self,
        current: StampedPtr<T>,
        new: StampedPtr<T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<StampedPtr<T>, StampedPtr<T>> {
        self.p.compare_exchange_weak(current, new, success, failure)
    }

    /// Fetches the value, and applies a function to it that returns an optional
    /// new value. Returns a `Result` of `Ok(previous_value)` if the function
    /// returned `Some(_)`, else `Err(previous_value)`.
    ///
    /// Note: This may call the function multiple times if the value has been
    /// changed from other threads in the meantime, as long as the function
    /// returns `Some(_)`, but the function will have been applied only once to
    /// the stored value.
    ///
    /// `fetch_update` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. The first describes the required ordering for
    /// when the operation finally succeeds while the second describes the
    /// required ordering for loads. These correspond to the success and failure
    /// orderings of [`AtomicStampedPtr::compare_exchange`] respectively.
    ///
    /// Using [`Acquire`] as success ordering makes the store part of this
    /// operation [`Relaxed`], and using [`Release`] makes the final successful
    /// load [`Relaxed`]. The (failed) load ordering can only be [`SeqCst`],
    /// [`Acquire`] or [`Relaxed`] and must be equivalent to or weaker than the
    /// success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atomic_stamped_ptr::{AtomicStampedPtr, Ordering};
    ///
    /// let ptr: *mut _ = &mut 5;
    /// let some_ptr = AtomicStampedPtr::new(ptr);
    ///
    /// let new: *mut _ = &mut 10;
    /// assert_eq!(some_ptr.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(ptr));
    /// let result = some_ptr.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| {
    ///     if x == ptr {
    ///         Some(new)
    ///     } else {
    ///         None
    ///     }
    /// });
    /// assert_eq!(result, Ok(ptr));
    /// assert_eq!(some_ptr.load(Ordering::SeqCst).ptr, new);
    /// ```
    #[inline]
    pub fn fetch_update<F>(
        &self,
        set_order: Ordering,
        fetch_order: Ordering,
        mut f: F,
    ) -> Result<*mut T, *mut T>
    where
        F: FnMut(*mut T) -> Option<*mut T>,
    {
        let mut prev = self.load(fetch_order);
        while let Some(next) = f(prev.ptr) {
            match self.compare_exchange_weak(prev, prev.successor(next), set_order, fetch_order) {
                Ok(x) => return Ok(x.ptr),
                Err(next_prev) => prev = next_prev,
            }
        }
        Err(prev.ptr)
    }
}

unsafe impl<T> Send for AtomicStampedPtr<T> {}
unsafe impl<T> Sync for AtomicStampedPtr<T> {}

#[derive(Debug, PartialEq, Eq)]
pub struct StampedPtr<T> {
    pub ptr: *mut T,
    pub version: usize,
}

impl<T> Clone for StampedPtr<T> {
    fn clone(&self) -> Self {
        Self { ..*self }
    }
}

impl<T> Copy for StampedPtr<T> {}

impl<T> Default for StampedPtr<T> {
    fn default() -> Self {
        Self::new(null_mut())
    }
}

impl<T> StampedPtr<T> {
    /// Creates a new [`StampedPtr`].
    #[inline]
    pub const fn new(ptr: *mut T) -> Self {
        Self::with_version(ptr, 0)
    }

    /// Creates a new [`StampedPtr`] with specified version.
    #[inline]
    pub const fn with_version(ptr: *mut T, version: usize) -> Self {
        Self { ptr, version }
    }

    /// Creates a new [`StampedPtr`] from an existing one as it's successor.
    #[inline]
    pub const fn successor(self, ptr: *mut T) -> Self {
        Self::with_version(ptr, self.next_version())
    }

    /// Returns a shared reference to the value.
    ///
    /// # Safety
    /// See Rust's doc.
    #[inline]
    pub unsafe fn as_ref(&self) -> Option<&T> {
        self.ptr.as_ref()
    }

    /// Returns a unique reference to the value.
    ///
    /// # Safety
    /// See Rust's doc.
    #[inline]
    pub unsafe fn as_mut(&mut self) -> Option<&mut T> {
        self.ptr.as_mut()
    }

    /// Casts to a pointer of another type.
    #[inline]
    pub const fn cast<U>(self) -> StampedPtr<U> {
        StampedPtr {
            ptr: self.ptr.cast(),
            version: self.version,
        }
    }

    /// Gets the next version of `self`.
    #[inline]
    pub const fn next_version(&self) -> usize {
        self.version.wrapping_add(1)
    }
}
