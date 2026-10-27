module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUMoves
public import CFSG.LocalAnalysis.StandardType.GGAssemblyEightDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

theorem ggStepTwoToralRound8_of_piece (hns : GGSpCoordModelNonsplitInput)
    (hswap : GGSUPieceSwapInput) (hshape : GGSUPieceShapeInput)
    (hPlus : GGStepTwoCoordModelOn .POmegaPlus) (hMinus : GGStepTwoCoordModelOn .POmegaMinus)
    (hRest : GGStepTwoToralWitnessRestInput) : GGStepTwoToralRound8 :=
  ⟨hns, ggStepTwoCoordModelOn_PSU_of_swap_shape hswap hshape, hPlus, hMinus, hRest⟩

end Lie

end CFSG.StandardType
