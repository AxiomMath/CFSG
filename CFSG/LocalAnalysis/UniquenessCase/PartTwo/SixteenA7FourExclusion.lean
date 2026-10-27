module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourLocalClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourSingleConjugate
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourComponentCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_false_of_a7Four_of_s15_eq_two
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2) : False := by
  have _hcomp := hcomp
  exact s168e3_false_of_a7Four_of_s15_eq_two_of_blockInvolutionBound c hrow hs
    (s168e3_block_involutionBound c hrow)

theorem s168e3_false_of_a7Four_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))) : False := by
  have hpos : 0 < s15 D.M V₀ V hV L := s15_Eleven_pos_s D c.setting.hyp151 hV
  have hle : s15 D.M V₀ V hV L ≤ 2 := s15_le_two_of_a7Four_component c hcomp hrow
  have hs : s15 D.M V₀ V hV L = 1 ∨ s15 D.M V₀ V hV L = 2 := by omega
  rcases hs with hs | hs
  · exact s168e3_false_of_a7Four_of_s15_eq_one c hrow hs
  · exact s168e3_false_of_a7Four_of_s15_eq_two c hcomp hrow hs

theorem s168e3_concl163F_of_a7Four_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))) : Concl163F D V₀ V hV L :=
  (s168e3_false_of_a7Four_component c hcomp hrow).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
