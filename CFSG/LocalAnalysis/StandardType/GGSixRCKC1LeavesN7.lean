module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesD1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortSpF4

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKK1II

@[expose] def RCKK2NbrRootSubShortRest
    : Prop :=
  RCKK2NbrRootSubShortAt .POmegaMinus

@[expose] def GGSixRootCommKnownLeavesN7
    : Prop :=
  RCKRP.RCKIntrinsicRoot ∧ RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧ RCKK2NbrRootSubShortRest ∧
    RCKK2FlagRootSub ∧ RCKK2NbrCollinear ∧ RCKRowK2 .III RCKPosShort ∧
    RCKRowK2 .IIp (RCKPosCent 96)

end CFSG.StandardType.RCKC1
