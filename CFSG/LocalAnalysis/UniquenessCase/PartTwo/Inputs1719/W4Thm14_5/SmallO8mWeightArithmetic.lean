module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

private theorem coprime_two_pow_add_one (e b : ℕ) (he : 0 < e) :
    Nat.Coprime (2 ^ e + 1) (2 ^ b) := by
  have heven : Even (2 ^ e) := Nat.even_pow.mpr ⟨even_two, he.ne'⟩
  exact (Nat.coprime_two_right.mpr heven.add_one).pow_right b

theorem pow_two_modEq_add_one_injective {e i j : ℕ}
    (he : 2 ≤ e) (hi : i < 2 * e) (hj : j < 2 * e)
    (h : Nat.ModEq (2 ^ e + 1) (2 ^ i) (2 ^ j)) : i = j := by
  by_contra hne
  wlog hij : i < j generalizing i j
  · exact this hj hi h.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hij) (Ne.symm hne))
  have hle : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hij.le
  have hdiv : 2 ^ e + 1 ∣ 2 ^ j - 2 ^ i := (Nat.modEq_iff_dvd' hle).mp h
  have hfactor : 2 ^ j - 2 ^ i = 2 ^ i * (2 ^ (j - i) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hij.le]
  rw [hfactor] at hdiv
  have hperiod := CFSG.CGT.Timmesfeld75.irr_two_mul_le_of_dvd (by omega : 0 < j - i)
    ((coprime_two_pow_add_one e i (by omega)).dvd_of_dvd_mul_left hdiv)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
