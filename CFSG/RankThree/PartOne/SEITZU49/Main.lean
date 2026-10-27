module

public import CFSG.RankThree.PartOne.SEITZU49.Shape
public import CFSG.RankThree.PartOne.SEITZU49.Big

public section

namespace CFSG.RankThree.PartOne.SEITZU49

open Matrix CFSG CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCEvenUnitaryFive
  CFSG.RankThree.PartOne.CTP

theorem psu5DiagPlane49_of_four (hFour : Gen49Four) : PSU5DiagPlane49 := by
  intro f K _ h h5 A hAel hAcard hAD hnab hshape
  have := h.finite
  have := h.charP
  have hK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  by_cases hf : f = 2
  · subst hf
    exact Shape.closure_fixUnion_of_shape49 h (by norm_num) h5
      (fun z hz hnz M hM => hFour K hK z hz hnz M hM) A hAel hnab hshape
  · have h1 := h.one_le
    have hf6 : 6 ≤ f := by
      by_contra hlt
      push Not at hlt
      interval_cases f <;> omega
    have hq3 : 3 < 2 ^ f := by
      have : 2 ^ 6 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf6
      omega
    exact Shape.closure_fixUnion_of_shape49 h hq3 h5
      (fun z hz hnz M hM => gen49Big_holds f K hK hf6 h5 z hz hnz M hM) A hAel hnab hshape

end CFSG.RankThree.PartOne.SEITZU49
