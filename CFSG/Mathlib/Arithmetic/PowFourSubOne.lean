module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Ring.Canonical

public section

namespace CFSG

theorem dvd_pow_four_sub_one_of_dvd_factor {q p : ℕ}
    (h : p ∣ q - 1 ∨ p ∣ q + 1 ∨ p ∣ q ^ 2 + 1) : p ∣ q ^ 4 - 1 := by
  have h2 : q ^ 2 - 1 = (q + 1) * (q - 1) := by rw [← sq_tsub_sq q 1, one_pow]
  have h4 : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by rw [← pow_mul], ← sq_tsub_sq (q ^ 2) 1, one_pow]
  rw [h4, h2]
  rcases h with h | h | h
  · exact (h.mul_left _).mul_left _
  · exact (h.mul_right _).mul_left _
  · exact h.mul_right _

end CFSG

end
