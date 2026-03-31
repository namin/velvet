import Velvet.Syntax
import Velvet.Std

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- for-in range test with break
method arrayContains (arr : Array Int) (target : Int) return (res : Bool)
  ensures res = true → ∃ k : Nat, k < arr.size ∧ arr[k]! = target
  ensures res = false → ∀ k : Nat, k < arr.size → arr[k]! ≠ target
  do
    let mut found : Bool := false
    for _x_idx in [:arr.size]
      invariant found = false → ∀ k : Nat, k < _x_idx → arr[k]! ≠ target
      invariant found = true → ∃ k : Nat, k < arr.size ∧ arr[k]! = target
    do
      let x := arr[_x_idx]!
      if x = target then
        found := true
        break
    return found

prove_correct arrayContains by
  loom_solve
