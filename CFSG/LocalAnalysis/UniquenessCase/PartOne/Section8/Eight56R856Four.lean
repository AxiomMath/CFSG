module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R856NormalFour

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xA858
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56SpineChain
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R69Setup4
import CFSG.LocalAnalysis.UniquenessCase.OpenThree.R856NonNormal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56SpineChainChoiceX

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

theorem r856_dataOfSetup4
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) : R856 (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) := by
  classical
  intro L hL h3 Q hQ hGamma
  by_cases hML : S.M ≤ Subgroup.normalizer (L : Set G)
  · exact UC22.r856_normal_dataOfSetup4 hS hU S hMS hPart hL hML h3 hQ hGamma
  by_cases hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M
  · exact Or.inl hsp
  by_cases hsl : IsSL3PiType (Bar2 L)
  · exact Or.inr hsl
  exfalso
  obtain ⟨P, hP, hQP⟩ := exists_sylow_three_ge_of_le hL.1.le hQ
  have hc : Cex856 (UC6.dataOfSetup4 hS hU S) L Q P :=
    ⟨hL, h3, hQ, hGamma, hsp, hsl, hP, hQP⟩
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  have h857 := UC22.R856NormalFour.list_dataOfSetup4 hS hU S hPart
  rcases r858_of_r857 hSg h857 L Q P hc with hNormal | ⟨h2, hcover⟩
  · exact hML hNormal
  have hfus := (UC22.R856NormalFour.r862_dataOfSetup4 hS hU S hPart L Q P hc).1
  obtain ⟨X, hX⟩ := exists_choiceX_of_controlsFusion (UC6.dataOfSetup4 hS hU S) hc hfus
  exact PartTwo.Three.R856NonNormal.false_of_cover_choice_two hSg
    (r6_9_dataOfSetup4 hS hU S hMS hPart.1) hX hcover h2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
