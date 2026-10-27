module

public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

theorem isSquare_mul_self_mul_iff {α : Type*} [Field α] {c q : α} (hc : c ≠ 0) :
    IsSquare (c * c * q) ↔ IsSquare q := by
  constructor
  · intro h
    have hinv : IsSquare ((c * c)⁻¹) := isSquare_inv.mpr (IsSquare.mul_self c)
    have h2 : IsSquare ((c * c)⁻¹ * (c * c * q)) := IsSquare.mul hinv h
    rwa [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hc hc), one_mul] at h2
  · intro h
    exact IsSquare.mul (IsSquare.mul_self c) h

end CFSG
