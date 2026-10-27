module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenB
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_20_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h12 : R16_12 D) (h13 : R16_13_1 D) (h13b : R16_13_2 D) (h14 : R16_14 D)
    (h16 : R16_16 D) (h18 : R16_18 D) (h19 : R16_19 D) : R16_20 D := by
  intro V₀ V L hV hC A g Δ hA hAg hΔ B U hBU
  obtain ⟨-, h0, -⟩ := h12 V₀ V L hV hC
  subst h0
  rcases h19 ⊥ V L hV hC with h2 | h9
  · have hS : Case168_2Small D ⊥ V hV L :=
      s16c167_twenty_two_small D hC (h13b ⊥ V L hV hC) h2
    have hk : D.k = 1 :=
      s15_Thirteen_k_eq_one_of_three_mem D hSg h1219 (by rw [h2.2.2]; exact Set.mem_singleton 3)
    obtain ⟨hB, hI, hcap⟩ :=
      s16c167_twenty_two D hk h13 h14 h18 hC hA hAg hΔ h2 hS (h16 ⊥ V L hV hC) hBU
    exact ⟨h2, hB, hI, hcap⟩
  · exact (s16c167_twenty_nine D h14 hC hA hAg hΔ h9).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
