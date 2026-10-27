module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Mathlib.GroupTheory.Basic

public section

namespace CFSG.Quasithin.SteinbergCD

open CFSG Subgroup

variable {H : Type*} [Group H]

theorem dvd_sub_one_or_dvd_add_one_of_dvd_mul_self_sub_one {k : ℤ}
    (h : (9 : ℤ) ∣ k * k - 1) : (9 : ℤ) ∣ k - 1 ∨ (9 : ℤ) ∣ k + 1 := by
  have h' : (k : ZMod 9) * (k : ZMod 9) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k * k - 1) 9).mpr (by exact_mod_cast h)
    push_cast at this
    exact sub_eq_zero.mp this
  have key : ∀ x : ZMod 9, x * x = 1 → x = 1 ∨ x = -1 := by decide
  rcases key _ h' with h1 | h1
  · left
    exact_mod_cast
      (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 9).mp (by push_cast; rw [h1, sub_self])
  · right
    exact_mod_cast
      (ZMod.intCast_zmod_eq_zero_iff_dvd (k + 1) 9).mp (by push_cast; rw [h1, neg_add_cancel])

end SteinbergCD

open Subgroup SteinbergCD

end CFSG.Quasithin
