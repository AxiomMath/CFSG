module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3AltBridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltFiveTripleRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltFiveTripleOneBot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltFiveTripleOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallComponentBounds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_concl163F_of_alt_five_sum_three
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : s16h_H5A5Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    Concl163F D V₀ V hV L := by
  classical
  obtain ⟨hA5, hsum⟩ := s16h_a5Sum_alt hrow
  have hle : s15 D.M V₀ V hV L ≤ 3 := s168e3_s_le_three_of_alt_five c hcomp hA5
  have hge : 1 ≤ s15 D.M V₀ V hV L := Om8Excl.one_le_s15 D.M V₀ V hV L
  have hs : s15 D.M V₀ V hV L = 1 ∨ s15 D.M V₀ V hV L = 2 ∨
      s15 D.M V₀ V hV L = 3 := by omega
  rcases hs with hs | hs | hs
  · by_cases hV₀ : V₀ = ⊥
    · exact (s168e3_false_of_sum_three_alt_five_of_v0_eq_bot c hcomp hrow hs hV₀).elim
    · exact (s168e3_false_of_sum_three_alt_five_of_v0_ne_bot c hcomp hrow hs hV₀).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (s168e3_case163_5_of_sum_three_a5 c hs hA5 hsum))))))
  · exact (s168e3_s15_ne_three_of_alt_five_sum_three c h82 hcomp hrow hs).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
