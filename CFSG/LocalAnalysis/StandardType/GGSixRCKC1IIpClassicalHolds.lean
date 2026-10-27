module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRec
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecClassical
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSL
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSp
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMAssembly

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.RCKRP

theorem rckIIpAt_classical_holds :
    RCKIIpAt RCKClassicalTag :=
  rckIIpAt_classical_of (rckLemmaFIIp_of_at fun t ht => by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact rckLemmaFIIpAt_PSL
    · exact rckLemmaFIIpAt_PSU
    · exact rckLemmaFIIpAt_PSp
    · exact rckLemmaFIIpAt_POmegaPlus
    · exact rckLemmaFIIpAt_POmegaMinus) rckCompModel_holds

end CFSG.StandardType.RCKC1
