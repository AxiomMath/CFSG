module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmCompZero

public section

namespace CFSG.StandardType

open Polynomial Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

theorem ggOmFrameCompInput_of_splitFour (hsf : GGOmSplitFourCentInput) : GGOmFrameCompInput := by
  intro K _ _ _ V _ _ _ p _ hp2 Q hQ hT A hAΩ hmax r F hr4 hF L β _ hL hcardL
  have hp : p.Prime := Fact.out
  have hx : OddOrderIsometry Q p (F.ι (ofAdd β)) := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd β)
  have hL' := SevOm.isComponentOf_isometryCentralizer hL
  obtain ⟨h, hh, hLF⟩ := SevOm.exists_le_supportedBlock hx hL'
  by_cases hX : h = X - 1
  · rw [hX] at hh hLF
    exact Or.inl (CoordOm.comp_fixed hsf hQ hp hp2 hAΩ F hr4 β hh hL' hLF hcardL)
  · exact Or.inr (CoordOm.comp_class hQ hT hp hp2 hAΩ hmax F hr4 hF β hh hX
      (SevOm.free_case hx hp hp2 hh hX hL' hLF) hcardL)

theorem ggOmCoordInput_of_inputs (hmove : GGOmFrameMoveInput) (hshape : GGOmFrameShapeInput)
    (hsf : GGOmSplitFourCentInput) : GGOmCoordInput :=
  ggOmCoordInput_of_frame hmove (ggOmFrameCompInput_of_splitFour hsf) hshape

section Certified

theorem ggStepTwoCoordModelOn_POmegaPlus_of_inputs (hmove : GGOmFrameMoveInput)
    (hshape : GGOmFrameShapeInput) (hsf : GGOmSplitFourCentInput) :
    GGStepTwoCoordModelOn .POmegaPlus :=
  ggStepTwoCoordModelOn_POmegaPlus_of_coord (ggOmCoordInput_of_inputs hmove hshape hsf)

theorem ggStepTwoCoordModelOn_POmegaMinus_of_inputs (hmove : GGOmFrameMoveInput)
    (hshape : GGOmFrameShapeInput) (hsf : GGOmSplitFourCentInput) :
    GGStepTwoCoordModelOn .POmegaMinus :=
  ggStepTwoCoordModelOn_POmegaMinus_of_coord (ggOmCoordInput_of_inputs hmove hshape hsf)

end Certified

end CFSG.StandardType
