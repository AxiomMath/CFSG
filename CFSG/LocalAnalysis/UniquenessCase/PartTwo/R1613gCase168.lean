module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10CardOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r1613g_card_ne_three_of_isLn {X : Type} [Group X] {m : ℕ} (h3 : 3 ≤ m) (h5 : m ≤ 5)
    (h : IsLn X m 1) : Nat.card X ≠ 3 := by
  have hc := CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two h
  rw [hc]
  interval_cases m <;> decide

variable {G : Type} [Group G] [Finite G]

theorem r1613g_case168_eight_of_card_three (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hcard : Nat.card ↥(lBar V₀ V hV L) = 3)
    (hrk : rk ↥(wTil V₀ V hV L) ≤ 2) (h : Concl168 D V₀ V hV L) : Case168_8 D V₀ V hV := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exfalso
    have := s16c167_card_isAlt_six h.2.1
    omega
  · exfalso
    obtain ⟨-, ⟨L₀, -, hshape⟩, -⟩ := h
    rcases hshape with ⟨n, hn5, hn11, -, hA, -⟩ | ⟨m, hm3, hm5, -, hL, -⟩ | ⟨-, hS, -⟩ |
      ⟨-, hO, -⟩ | ⟨-, hO, -⟩
    · have h2 := s16c167_two_mul_card_isAlt (by omega) hA
      have h3 := Nat.factorial_le hn5
      have h4 : Nat.factorial 5 = 120 := by decide
      omega
    · exact r1613g_card_ne_three_of_isLn hm3 hm5 hL hcard
    · have := s16c1610_card_of_isSpn_six hS
      omega
    · have := s16c167_card_isOmegaMinus_six hO
      omega
    · have := s16c1610_card_of_isOmegaMinus_eight hO
      omega
  · exfalso
    have := h.1.2.1
    omega
  · exfalso
    obtain ⟨p, r, hp, hr, hat, -, -⟩ := h
    rcases hp with rfl | rfl
    · have h3 := s16c167_card_isElemAbelianOfRank hat
      have h4 := Nat.pow_le_pow_right (show 0 < 3 by norm_num) (show 2 ≤ r by omega)
      omega
    · have h3 := s16c167_card_isElemAbelianOfRank hat
      have h4 := Nat.pow_le_pow_right (show 0 < 7 by norm_num) (show 2 ≤ r by omega)
      omega
  · exfalso
    have := s16c1610_card_of_isOmegaPlus_four_two h.2.1
    omega
  · exfalso
    obtain ⟨-, hsh, -, -⟩ := h
    rcases hsh with ⟨hA, -⟩ | ⟨hL, -⟩
    · have := Om8Excl.card_isAlt_five hA
      omega
    · have := Om8Excl.card_isL3_one hL
      omega
  · exfalso
    have := Om8Excl.card_isL3_one h.2.1
    omega
  · exact h
  · exfalso
    have := Om8Excl.card_isL3_one h.2.1
    omega
  · exfalso
    obtain ⟨p, hp, hcyc, hrk', -, -, -⟩ := h
    rcases hp with rfl | rfl
    · rw [s16c1610_dParam_three] at hrk'
      omega
    · have := hcyc.2
      omega
  · exfalso
    have := h.1.2
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
