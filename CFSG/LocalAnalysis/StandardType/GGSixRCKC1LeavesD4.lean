module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesShort

public section

namespace CFSG.StandardType.RCKC1

@[expose] def GGSixRootCommKnownLeavesD4 :
    Prop :=
  RCKRP.RCKIntrinsicRoot ∧ RCKRowK1 .II RCKPosRootElt ∧ RCKRowK1 .III RCKPosShort ∧
    RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧ RCKK2NbrRootSubShort ∧ RCKK2FlagRootSub ∧
    RCKK2NbrCollinear ∧ RCKRowK2 .III RCKPosShort ∧ RCKRowK2 .IIp (RCKPosCent 96)

end CFSG.StandardType.RCKC1
