module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesN7
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1III

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKK1II

@[expose] def GGSixRootCommKnownLeavesF8
    : Prop :=
  RCKRP.RCKIntrinsicRoot ∧ RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧ RCKK2NbrRootSubShortRest ∧
    RCKK2NbrCollinear ∧ RCKRowK2IIIAtTwoRemaining ∧ RCKRowK2 .IIp (RCKPosCent 96)

end CFSG.StandardType.RCKC1
