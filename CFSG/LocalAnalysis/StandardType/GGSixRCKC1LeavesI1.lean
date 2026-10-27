module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesN7
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1III
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKK1II

@[expose] def GGSixRootCommKnownLeavesI1
    : Prop :=
  RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧ RCKRowK2IIIAtTwoRemaining ∧
    RCKIIpAt RCKRP.RCKClassicalTag

end CFSG.StandardType.RCKC1
