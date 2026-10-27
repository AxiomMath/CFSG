module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaRest
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6Twisted
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLHolds

public section

namespace CFSG.StandardType

theorem ggAutStructureRest_holds : GGAutStructureRest :=
  ggAutStructureRest_of_E6_twistedE6_triality plusFourTrialityInput_holds
    ggAutModelAt_E6 ggAutModelAt_twistedE6

theorem ggAutStructureInput_holds : GGAutStructureInput :=
  ggAutStructureInput_of_rest ggAutStructureRest_holds

theorem ggSixStepThreeCInput_of_F4 (hF4 : GGSixStepThreeCFourInput) : GGSixStepThreeCInput :=
  ggSixStepThreeCInput_of_aut ggAutStructureInput_holds hF4

end CFSG.StandardType
