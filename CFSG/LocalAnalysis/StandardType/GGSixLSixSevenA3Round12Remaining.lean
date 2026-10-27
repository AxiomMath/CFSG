module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3Round12Reduction
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3PSpEntry
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3PSUEntry

public section

namespace CFSG.StandardType

section Assembly

theorem ggSixLSixSevenConjA3Round12_of_remaining_three (hE6 : GGSixLSixSevenConjA3At .E6)
    (hF4 : GGSixLSixSevenConjA3At .F4) (hTw : GGSixLSixSevenConjA3At .twistedE6) :
    GGSixLSixSevenConjA3Round12 :=
  ggSixLSixSevenConjA3Round12_of_remaining hE6 ggSixLSixSevenConjA3At_PSU
    ggSixLSixSevenConjA3At_PSp hF4 hTw

end Assembly

end CFSG.StandardType
