module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesD2

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKK1II

@[expose] def GGSixRootCommKnownLeavesD1 :
    Prop :=
  RCKRP.RCKIntrinsicRoot ∧ RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧ RCKK2NbrRootSubShort ∧
    RCKK2FlagRootSub ∧ RCKK2NbrCollinear ∧ RCKRowK2 .III RCKPosShort ∧
    RCKRowK2 .IIp (RCKPosCent 96)

end CFSG.StandardType.RCKC1
