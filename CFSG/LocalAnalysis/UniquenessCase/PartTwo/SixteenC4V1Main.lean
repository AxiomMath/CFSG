module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1End
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c4v1_holds (D : Data G) (hstd : s16c4v1_Std D) : Case167_4_V1Eq D := by
  intro V₀ V L hV hS h4 h0
  subst h0
  by_contra hne
  obtain ⟨F⟩ := Sixteen24.exists_uFrame_v1Sub_of_case4 h4
  let S : s16c4v1_Sit D V L hV := ⟨hS, h4, hne, F⟩
  by_cases hsc : ∃ (z : G) (ω : S.F.K), s16c4v1_ScalarOf S z ω
  · obtain ⟨z, ω, hz⟩ := hsc
    exact s16c4v1_scalar_false S hstd hz
  · exact s16c4v1_noScalar_false S hstd hsc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
