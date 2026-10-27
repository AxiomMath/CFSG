module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUInMoves
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUInShape

public section

namespace CFSG.StandardType

section Model

theorem ggStepTwoCoordModelOn_PSU_holds : GGStepTwoCoordModelOn .PSU :=
  ggStepTwoCoordModelOn_PSU_of_swap_shape ggSUPieceSwapInput_holds ggSUPieceShapeInput_holds

theorem ggStepTwoToralWitnessOn_PSU_holds : GGStepTwoToralWitnessOn .PSU :=
  ggStepTwoToralWitnessOn_of_coordModel ggStepTwoCoordModelOn_PSU_holds

end Model

end CFSG.StandardType
