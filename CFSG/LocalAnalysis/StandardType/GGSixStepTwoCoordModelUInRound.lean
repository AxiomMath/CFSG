module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUIn
public import CFSG.LocalAnalysis.StandardType.GGAssemblyNineDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

theorem ggStepTwoToralRound8_of_rest (hns : GGSpCoordModelNonsplitInput)
    (hPlus : GGStepTwoCoordModelOn .POmegaPlus) (hMinus : GGStepTwoCoordModelOn .POmegaMinus)
    (hRest : GGStepTwoToralWitnessRestInput) : GGStepTwoToralRound8 :=
  ⟨hns, ggStepTwoCoordModelOn_PSU_holds, hPlus, hMinus, hRest⟩

theorem ggStepTwoToralRound9_of_rest (hZc : GGSpNsZeroContInput) (hXc : GGSpNsClassContInput)
    (hPlus : GGStepTwoCoordModelOn .POmegaPlus) (hMinus : GGStepTwoCoordModelOn .POmegaMinus)
    (hRest : GGStepTwoToralWitnessRestInput) : GGStepTwoToralRound9 :=
  ⟨hZc, hXc, ggStepTwoCoordModelOn_PSU_holds, hPlus, hMinus, hRest⟩

end Lie

end CFSG.StandardType
