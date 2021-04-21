# atomic-stamped-ptr

AtomicPtr with stamp to avoid [ABA problem](https://en.wikipedia.org/wiki/ABA_problem)

### Examples
```rust
use atomic_stamped_ptr::{AtomicStampedPtr, StampedPtr, Ordering};
let some_ptr  = AtomicStampedPtr::new(&mut 5);
let other_ptr = &mut 10;
let old_stamped_ptr = some_ptr.load(Ordering::Relaxed);
some_ptr.store(old_stamped_ptr.successor(other_ptr), Ordering::Relaxed);
// or
some_ptr.store(StampedPtr::new(other_ptr), Ordering::Relaxed);
```

License: MIT
