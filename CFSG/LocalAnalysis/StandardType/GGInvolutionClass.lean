module

public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSU

public section

namespace CFSG.StandardType

section Inputs

theorem ggSixRootFusionWitnessInputFor_linearUnitary_of_rep (hSLrep : GGSixRootFusionSLRepInput)
    (hSUrep : GGSixRootFusionSURepInput) :
    GGSixRootFusionWitnessInputFor GGLinearUnitaryTag :=
  ggSixRootFusionWitnessInputFor_linearUnitary ggSLInvolutionClassInput hSLrep
    ggSUInvolutionClassInput ggSURootClassInput hSUrep

end Inputs

end CFSG.StandardType
