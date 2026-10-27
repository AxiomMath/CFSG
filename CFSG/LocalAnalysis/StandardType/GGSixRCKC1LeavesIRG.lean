module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG

public section

namespace CFSG.StandardType.RCKC1

@[expose] def GGSixRootCommKnownLeavesIRG :
    Prop :=
  RCKRP.RCKIntrinsicRoot ∧ RCKRowK1 .II RCKPosRootElt ∧ RCKRowK1 .III RCKPosShort ∧
    RCKRowK1 .IIp (RCKPosCent 96) ∧ RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧ RCKK2NbrRootSub ∧
    RCKK2FlagRootSub ∧ RCKK2NbrCollinear ∧ RCKRowK2 .III RCKPosShort ∧ RCKRowK2 .IIp (RCKPosCent 96)

end CFSG.StandardType.RCKC1
