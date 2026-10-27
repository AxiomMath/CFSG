module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.TransferInstance
public import Mathlib.Algebra.Ring.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Right near-fields

This file contains the low-level algebraic definition used by Peterfalvi
Appendix II and by external finite-group classification results.
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixII

universe u

/-- A (right) near-field: addition is commutative, the nonzero elements form a
group, and multiplication distributes over addition in its left argument. -/
public class RightNearField (F : Type u) extends AddCommGroup F, GroupWithZero F where
  right_distrib : ∀ a b c : F, (a + b) * c = a * c + b * c


/-- The only roots of `x ^ 2 = 1` in a right near-field are `1` and `-1`. -/
public theorem rightNearField_eq_one_or_eq_neg_one_of_sq_eq_one
    {F : Type u} [RightNearField F] {x : F} (hx : x ^ 2 = 1) :
    x = 1 ∨ x = -1 := by
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  right
  by_contra hxneg
  have hsum : 1 + x ≠ 0 := by
    intro hzero
    exact hxneg (eq_neg_of_add_eq_zero_right hzero)
  have hmul : (1 + x) * x = (1 + x) * 1 := by
    calc
      (1 + x) * x = 1 * x + x * x := RightNearField.right_distrib 1 x x
      _ = x + 1 := by rw [one_mul, ← pow_two, hx]
      _ = 1 + x := add_comm x 1
      _ = (1 + x) * 1 := (mul_one (1 + x)).symm
  exact hx1 (mul_left_cancel₀ hsum hmul)

end PFAppendixII
end CFSG.BenderSuzuki
