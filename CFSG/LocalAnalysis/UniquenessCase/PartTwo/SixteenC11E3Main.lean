module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Case1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Case2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Case6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Case7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Case8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Case9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Case11
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Shared
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Normal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_holds (hH1 : H1SpSixNatural) (hGap : S1611e3V1SixGap) (D : Data G)
    (h : S1611e3Std D) : R16_11 D := by
  intro V₀ V L hV hc
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have h1610 : R16_10_2 D := h.r16_10_2 h125
  have h169 : R16_9 D := h.r16_9 h125
  have hbot : v1Sub D.M V₀ V hV L ≠ V₀ → V₀ = ⊥ := fun hv => by
    by_contra h0
    exact hv (v1Sub_of_ne_bot D.M V₀ V hV L h0)
  rcases hc.concl168 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · by_cases hv : v1Sub D.M V₀ V hV L = V₀
    · exact s1611e3_normalizer_le_of_case1_v1eq h hc h1 hv
    · have h0 := hbot hv
      subst h0
      exact s1611e3_normalizer_le_of_v1ne hH1 hGap h hc (Or.inl h1) hv
  · by_cases hv : v1Sub D.M V₀ V hV L = V₀
    · exact s1611e3_normalizer_le_of_case2 h hc ((s16e_case168_2Star_iff D V₀ V L hV hv).1 h2)
    · have h0 := hbot hv
      subst h0
      exact s1611e3_normalizer_le_of_v1ne hH1 hGap h hc (Or.inr (Or.inl h2)) hv
  · exact s16c11_normalizer_le_of_case3 D h.h61 h1610 h169 hc h3
  · exact s16c11_normalizer_le_of_case4 D h.h61 h1610 h169 hc h4
  · by_cases hv : v1Sub D.M V₀ V hV L = V₀
    · exact s1611e3_normalizer_le_of_case5 h hc ((s16e_case168_5Star_iff D V₀ V L hV hv).1 h5)
    · have h0 := hbot hv
      subst h0
      exact s1611e3_normalizer_le_of_v1ne hH1 hGap h hc (Or.inr (Or.inr h5)) hv
  · exact s1611e3_normalizer_le_of_case6 h hc h6
  · exact s1611e3_normalizer_le_of_case7 h hc h7
  · exact s1611e3_normalizer_le_of_case8 D h.h61 h1610 h169 hc h8
  · exact s1611e3_normalizer_le_of_case9 h hc h9
  · exact s16c11_normalizer_le_of_case10 D h.h61 h1610 h169 hc h10
  · exact s1611e3_normalizer_le_of_case11 D h.h1217 h.h61 h1610 h169 hc h11

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
