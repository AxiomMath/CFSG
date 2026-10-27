module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

private theorem ferm_two_pow_eq_one {r n : ℕ} (h : r ∣ 2 ^ n - 1) : (2 : ZMod r) ^ n = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero] at h
  simpa using h

private theorem ferm_two_pow_eq_neg_one {r k : ℕ} (h : r = 2 ^ k + 1) :
    (2 : ZMod r) ^ k = -1 := by
  have h0 : ((2 ^ k + 1 : ℕ) : ZMod r) = 0 := by
    rw [← h]
    exact ZMod.natCast_self r
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem not_dvd_two_pow_sub_one_of_eq_two_pow_add_one {r k n : ℕ} (hr : r.Prime)
    (hrk : r = 2 ^ k + 1) (hn : Odd n) : ¬ r ∣ 2 ^ n - 1 := by
  intro hdvd
  have : Fact (1 < r) := ⟨hr.one_lt⟩
  have hn1 := ferm_two_pow_eq_one hdvd
  have hk := ferm_two_pow_eq_neg_one hrk
  have hodd : Odd (orderOf (2 : ZMod r)) := hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one hn1)
  have h2k : orderOf (2 : ZMod r) ∣ 2 * k :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul', hk, neg_one_sq])
  have hdk : orderOf (2 : ZMod r) ∣ k := (Nat.coprime_two_right.2 hodd).dvd_of_dvd_mul_left h2k
  have h11 : (-1 : ZMod r) = 1 := hk.symm.trans (orderOf_dvd_iff_pow_eq_one.1 hdk)
  have h20 : (2 : ZMod r) = 0 := by
    rw [← one_add_one_eq_two]
    nth_rw 1 [← h11]
    exact neg_add_cancel 1
  rw [h20, zero_pow hn.pos.ne'] at hn1
  exact zero_ne_one hn1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
