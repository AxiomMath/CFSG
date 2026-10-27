module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRest
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUHolds
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpHolds
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFour

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank


theorem ggAutStructureRest_of_E6_twistedE6 (h4 : GGAutModelPlusFourInput)
    (hE6 : GGAutModelAt .E6) (h2E6 : GGAutModelAt .twistedE6) : GGAutStructureRest :=
  ggAutStructureRest_of_models ggAutStructureAt_PSU ggAutStructureAt_PSp
    (ggAutModelAt_POmegaPlus_of_four h4) ggAutModelAt_POmegaMinus hE6 h2E6

theorem ggAutStructureRest_of_E6_twistedE6_triality (hT : PlusFourTrialityInput)
    (hE6 : GGAutModelAt .E6) (h2E6 : GGAutModelAt .twistedE6) : GGAutStructureRest :=
  ggAutStructureRest_of_E6_twistedE6 (plusFourInput_of_triality hT) hE6 h2E6

end CFSG.StandardType
