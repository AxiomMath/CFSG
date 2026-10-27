module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Numerics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour (dParam_eq_of_small)

theorem two_le_dParam {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 2 ≤ dParam p := by
  have : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < dParam p := dParam_pos hp hp2
  have hne : dParam p ≠ 1 := by
    intro h1
    have h2 : (2 : ZMod p) = 1 := by
      have := pow_dParam p
      rwa [h1, pow_one] at this
    have h3 : (2 : ZMod p) - 1 = 0 := by rw [h2, sub_self]
    have h4 : ((1 : ℕ) : ZMod p) = 0 := by
      have h5 : (2 : ZMod p) - 1 = ((1 : ℕ) : ZMod p) := by norm_num
      rwa [h5] at h3
    exact hp.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p).mp h4)
  omega

theorem odd_prime_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ 11 ≤ p := by
  have hpge : 3 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  rcases lt_or_ge p 11 with hlt | hge
  · have hp3 : p = 3 ∨ p = 5 ∨ p = 7 := by
      interval_cases p <;> try omega
      all_goals norm_num at hp
    tauto
  · exact Or.inr (Or.inr (Or.inr hge))

theorem sixteen_le_pow_mul_dParam {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : 0 < N)
    (hN3 : p = 3 → 2 ≤ N) : 16 ≤ p ^ N * dParam p := by
  rcases odd_prime_cases hp hp2 with h | h | h | h11
  · subst h
    have h2 : 2 ≤ N := hN3 rfl
    rw [dParam_eq_of_small.1]
    have hpow : 9 ≤ 3 ^ N := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) h2
    calc 16 ≤ 9 * 2 := by norm_num
      _ ≤ 3 ^ N * 2 := Nat.mul_le_mul_right 2 hpow
  · subst h
    rw [dParam_eq_of_small.2.1]
    have hpow : 5 ≤ 5 ^ N := by
      calc 5 = 5 ^ 1 := (pow_one 5).symm
        _ ≤ 5 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 16 ≤ 5 * 4 := by norm_num
      _ ≤ 5 ^ N * 4 := Nat.mul_le_mul_right 4 hpow
  · subst h
    rw [dParam_eq_of_small.2.2.1]
    have hpow : 7 ≤ 7 ^ N := by
      calc 7 = 7 ^ 1 := (pow_one 7).symm
        _ ≤ 7 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 16 ≤ 7 * 3 := by norm_num
      _ ≤ 7 ^ N * 3 := Nat.mul_le_mul_right 3 hpow
  · have hd : 2 ≤ dParam p := two_le_dParam hp hp2
    have hpow : 11 ≤ p ^ N := by
      calc 11 ≤ p := h11
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ N := Nat.pow_le_pow_right (by omega) (by omega)
    calc 16 ≤ 11 * 2 := by norm_num
      _ ≤ p ^ N * dParam p := Nat.mul_le_mul hpow hd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
