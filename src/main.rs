use vstd::prelude::*;

verus! {

// 1. introduce failing ensures
// 2. move up assertion
// 3. fix proof (manual)   `assert(fibo(j) == fibo((j-1) as nat) + fibo((j-2) as nat));`
// 4. remove dead assertion

pub open spec fn fibo(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else if n == 1 { 1 }
    else { fibo((n - 2) as nat) + fibo((n - 1) as nat) }
}

proof fn lemma_fibo_is_monotonic(i: nat, j: nat)
    requires i <= j,
    ensures fibo(i) <= fibo(j),
    decreases j - i
{
    if i < 2 && j < 2 {
        assert(fibo(i) <= fibo(j));
    } else if i == j {
        assert(fibo(i) <= fibo(j));
    } else if i == j - 1 {
        lemma_fibo_is_monotonic(i, (j - 1) as nat);
        assert(fibo(j) == fibo((j-1) as nat) + fibo((j-2) as nat));
        assert(fibo(i) <= fibo(j));
    } else {
        lemma_fibo_is_monotonic(i, (j - 1) as nat);
        lemma_fibo_is_monotonic(i, (j - 2) as nat);
        assert(fibo(i) <= fibo(j));
    };
    assert(fibo(i) <= fibo(j));
}



// proof fn lemma_fibo_is_monotonic(i: nat, j: nat)
//     requires i <= j,
//     ensures fibo(i) <= fibo(j),
//     decreases j - i
// {
//     if i < 2 && j < 2{
//     } else if i == j {
//     } else if i == j -1 {
//       lemma_fibo_is_monotonic(i, (j - 1) as nat);
//       // now fibo(i) <= fibo(j-1);
//       assert(fibo(j) == fibo((j-1) as nat) + fibo((j-2) as nat)); // missing proof
//       assert(fibo(i) <= fibo(j));
//     } else {
//       lemma_fibo_is_monotonic(i, (j - 1) as nat);
//       lemma_fibo_is_monotonic(i, (j - 2) as nat);
//     }
// }

} //verus


fn main() {
}
