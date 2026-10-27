module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank

theorem exists_two_pow_of_fermatOrMersenne {p : ℕ} (hp : IsFermatOrMersennePrime p)
    (hp3 : p ≠ 3) : ∃ (ε : ℤ) (j : ℕ), (p : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) ∧
      (p : ℤ) - ε = 2 ^ j := by
  rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (by rw [hk]; norm_num) hp3
    · have h2 : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk0
      have h4 : (4 : ℤ) ∣ 2 ^ 2 ^ k := by
        have := pow_dvd_pow (2 : ℤ) h2
        norm_num at this
        exact this
      refine ⟨1, 2 ^ k, ?_, Or.inl rfl, by rw [hk]; push_cast; ring⟩
      rw [Int.modEq_iff_dvd, hk]
      push_cast
      rw [show (1 : ℤ) - (2 ^ 2 ^ k + 1) = -(2 ^ 2 ^ k) by ring]
      exact dvd_neg.mpr h4
  · have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h4 : (4 : ℤ) ∣ 2 ^ k := by
      have := pow_dvd_pow (2 : ℤ) hk2
      norm_num at this
      exact this
    have hcast : (p : ℤ) = 2 ^ k - 1 := by
      rw [hk, Nat.cast_sub h1]
      push_cast
      ring
    refine ⟨-1, k, ?_, Or.inr rfl, by rw [hcast]; ring⟩
    rw [Int.modEq_iff_dvd, hcast, show (-1 : ℤ) - (2 ^ k - 1) = -(2 ^ k) by ring]
    exact dvd_neg.mpr h4

theorem ne_two_of_fermatOrMersenne {p : ℕ} (hp : IsFermatOrMersennePrime p) : p ≠ 2 := by
  rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  · have : 2 ≤ 2 ^ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    omega
  · have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

end CFSG.Quasithin.H13.KG14726

end
