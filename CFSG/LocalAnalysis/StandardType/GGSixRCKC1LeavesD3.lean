module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesD4

public section

namespace CFSG.StandardType.RCKC1

@[expose] def GGSixRootCommKnownLeavesD3 :
    Prop :=
  RCKRP.RCKIntrinsicRoot ∧ RCKRowK1 .II RCKPosRootElt ∧ RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧
    RCKK2NbrRootSubShort ∧ RCKK2FlagRootSub ∧ RCKK2NbrCollinear ∧ RCKRowK2 .III RCKPosShort ∧
    RCKRowK2 .IIp (RCKPosCent 96)

end CFSG.StandardType.RCKC1
