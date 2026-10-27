module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaH

public section

namespace CFSG.StandardType.RCKC1

@[expose] def GGSixRootCommKnownLeavesShort :
    Prop :=
  RCKRP.RCKIntrinsicRoot ∧ RCKRowK1 .II RCKPosRootElt ∧ RCKRowK1 .III RCKPosShort ∧
    RCKRowK1 .IIp (RCKPosCent 96) ∧ RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧
    RCKK2NbrRootSubShort ∧ RCKK2FlagRootSub ∧ RCKK2NbrCollinear ∧ RCKRowK2 .III RCKPosShort ∧
    RCKRowK2 .IIp (RCKPosCent 96)

end CFSG.StandardType.RCKC1
