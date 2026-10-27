module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16t3_val_M :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 3 ∣ 197406720) ∧ ¬ 7 ^ 2 ∣ 197406720 := by
  refine ⟨fun p hp _ hdvd => ?_, by norm_num⟩
  have hpdvd : p ∣ 197406720 := dvd_trans (dvd_pow_self p (by norm_num : 3 ≠ 0)) hdvd
  have hfac : (197406720 : ℕ) = 2 ^ 12 * (3 ^ 4 * (5 * (7 * 17))) := by norm_num
  rw [hfac] at hpdvd
  have key : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 := by
    rcases hp.dvd_mul.mp hpdvd with h1 | h1
    · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h1)
    rcases hp.dvd_mul.mp h1 with h2 | h2
    · exact Or.inr (Or.inl (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three h2))
    rcases hp.dvd_mul.mp h2 with h3 | h3
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h3)))
    rcases hp.dvd_mul.mp h3 with h4 | h4
    · exact Or.inr (Or.inr (Or.inr
        (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h4))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : (17 : ℕ).Prime)).mp h4))))
  rcases key with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)

private theorem s16t3_val_of_dvd_M {N : ℕ} (hNM : N ∣ 197406720) :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 3 ∣ N) ∧ ¬ 7 ^ 2 ∣ N :=
  ⟨fun p hp hp5 hdvd => s16t3_val_M.1 p hp hp5 (dvd_trans hdvd hNM),
    fun h => s16t3_val_M.2 (dvd_trans h hNM)⟩

theorem s16t3_val_card_om {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (hX : ∃ n : ℕ, (IsSpn X n 1 ∧ n < 8) ∨ (IsOmegaPlus X n 1 ∧ n < 8) ∨
      (IsOmegaMinus X n 1 ∧ n < 10)) :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 3 ∣ Nat.card X) ∧ ¬ 7 ^ 2 ∣ Nat.card X := by
  obtain ⟨n, hn | hn | hn⟩ := hX
  · obtain ⟨hSp, hn8⟩ := hn
    have hn6 : 6 ≤ n := s16k_six_le_of_isSpn hq hSp
    have hn_eq : n = 6 := by obtain ⟨r, hr⟩ := hSp.1; omega
    subst hn_eq
    rw [s16c1610_card_of_isSpn_six hSp]
    exact s16t3_val_of_dvd_M (by norm_num)
  · obtain ⟨hOP, hn8⟩ := hn
    have hn6 : 6 ≤ n := s16k_six_le_of_isOmegaPlus hq hOP
    have hn_eq : n = 6 := by obtain ⟨r, hr⟩ := hOP.1; omega
    subst hn_eq
    have hAlt : UC22.IsAlt X 8 := s15k_omp6_isAlt8 hOP
    have hcard : Nat.card X = 20160 := by
      rw [s15k_six_alt_card hAlt (by norm_num)]
      norm_num [Nat.factorial]
    rw [hcard]
    exact s16t3_val_of_dvd_M (by norm_num)
  · obtain ⟨hOM, hn10⟩ := hn
    have hn4 : 4 ≤ n := s16k_four_le_of_isOmegaMinus hq hOM
    have hn_eq : n = 4 ∨ n = 6 ∨ n = 8 := by obtain ⟨r, hr⟩ := hOM.1; omega
    rcases hn_eq with rfl | rfl | rfl
    · have hAlt : UC22.IsAlt X 5 := s16k_isAlt_five_of_isOmegaMinus_four hOM
      have hcard : Nat.card X = 60 := by
        rw [s15k_six_alt_card hAlt (by norm_num)]
        norm_num [Nat.factorial]
      rw [hcard]
      exact s16t3_val_of_dvd_M (by norm_num)
    · rw [(s15k_six_om6 hOM).1]
      exact s16t3_val_of_dvd_M (by norm_num)
    · rw [s16c1610_card_of_isOmegaMinus_eight hOM]
      exact s16t3_val_of_dvd_M (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
