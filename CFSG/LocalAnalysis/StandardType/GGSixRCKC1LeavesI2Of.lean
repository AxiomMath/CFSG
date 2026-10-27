module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesI2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAssembly
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpClassicalHolds
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesF8
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesI1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesZ7

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKK1II
open CFSG.Open (StatedLieTag)

theorem ggSixRootCommKnownLeavesI1_of_i2
    (h : GGSixRootCommKnownLeavesI2) : GGSixRootCommKnownLeavesI1 := by
  obtain ⟨hE, hEII, h3⟩ := h
  exact ⟨RCKRP.rckRootPosKnownFlag_of_at RCKRP.rckRPAt_classical_holds hE,
    RCKRP.rckRootPosKnownII_of_at RCKRP.rckRPIIAt_classical_holds hEII, h3,
    rckIIpAt_classical_holds⟩

end CFSG.StandardType.RCKC1
