module

public import Mathlib.Data.ZMod.Basic
import CFSG.Quasithin.Vol2.Ch12Sec6P31WNT
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.NumberTheory

theorem two_pow_eq_neg_one_zmod {r n : ℕ} (hrn : r ∣ 2 ^ n + 1) : (2 : ZMod r) ^ n = -1 := by
  have h : ((2 ^ n + 1 : ℕ) : ZMod r) = 0 := (CharP.cast_eq_zero_iff (ZMod r) r _).2 hrn
  push_cast at h
  linear_combination h

theorem not_dvd_two_pow_sub_one_of_dvd_two_pow_add_one {r n m : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n + 1) (hm : Odd m) : ¬ r ∣ 2 ^ m - 1 := fun h =>
  CFSG.Quasithin.H13.P31NT.not_two_pow_odd_modEq_one hr hr2 hrn hm
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 h).symm

theorem not_dvd_two_pow_add_one_of_even {r n m : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hn : Odd n) (hrn : r ∣ 2 ^ n + 1) (hm : Even m) : ¬ r ∣ 2 ^ m + 1 := by
  intro hrm
  have : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  have h1 : (2 : ZMod r) ^ n = -1 := two_pow_eq_neg_one_zmod hrn
  have h2 : (2 : ZMod r) ^ m = -1 := two_pow_eq_neg_one_zmod hrm
  apply ZMod.neg_one_ne_one (n := r)
  calc (-1 : ZMod r) = ((2 : ZMod r) ^ m) ^ n := by rw [h2, hn.neg_one_pow]
    _ = ((2 : ZMod r) ^ n) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ = 1 := by rw [h1, hm.neg_one_pow]

theorem eleven_le_of_dvd_two_pow_add_one {r n : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hn : Odd n)
    (hrn : r ∣ 2 ^ n + 1) : 11 ≤ r := by
  have hr2 : r ≠ 2 := by omega
  by_contra hlt
  have h5 : r ≠ 5 := by
    rintro rfl
    exact not_dvd_two_pow_add_one_of_even hr hr2 hn hrn (m := 2) even_two (by norm_num)
  have h7 : r ≠ 7 := by
    rintro rfl
    exact not_dvd_two_pow_sub_one_of_dvd_two_pow_add_one hr hr2 hrn (m := 3) (by decide)
      (by norm_num)
  interval_cases r <;> first | exact h5 rfl | exact h7 rfl | norm_num at hr

end CFSG.NumberTheory
