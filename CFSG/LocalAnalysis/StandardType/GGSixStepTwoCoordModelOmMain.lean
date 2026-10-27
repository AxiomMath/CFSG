module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmShape
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmSplitFour

public section

namespace CFSG.StandardType

theorem ggOmFrameCompInput_holds : GGOmFrameCompInput :=
  ggOmFrameCompInput_of_splitFour ggOmSplitFourCentInput_holds

theorem ggOmCoordInput_of_move (hmove : GGOmFrameMoveInput) : GGOmCoordInput :=
  ggOmCoordInput_of_move_splitFour hmove ggOmSplitFourCentInput_holds

section Certified

theorem ggStepTwoCoordModelOn_POmegaPlus_of_move (hmove : GGOmFrameMoveInput) :
    GGStepTwoCoordModelOn .POmegaPlus :=
  ggStepTwoCoordModelOn_POmegaPlus_of_coord (ggOmCoordInput_of_move hmove)

theorem ggStepTwoCoordModelOn_POmegaMinus_of_move (hmove : GGOmFrameMoveInput) :
    GGStepTwoCoordModelOn .POmegaMinus :=
  ggStepTwoCoordModelOn_POmegaMinus_of_coord (ggOmCoordInput_of_move hmove)

theorem ggStepTwoToralWitnessOn_POmegaPlus_of_move (hmove : GGOmFrameMoveInput) :
    GGStepTwoToralWitnessOn .POmegaPlus :=
  ggStepTwoToralWitnessOn_of_coordModel (ggStepTwoCoordModelOn_POmegaPlus_of_move hmove)

theorem ggStepTwoToralWitnessOn_POmegaMinus_of_move (hmove : GGOmFrameMoveInput) :
    GGStepTwoToralWitnessOn .POmegaMinus :=
  ggStepTwoToralWitnessOn_of_coordModel (ggStepTwoCoordModelOn_POmegaMinus_of_move hmove)

end Certified

end CFSG.StandardType
