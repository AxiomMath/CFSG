module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesN7
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1III
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKK1II

@[expose] def GGSixRootCommKnownLeavesI2
    : Prop :=
  RCKRP.RCKRPAt GGExcFive ∧ RCKRP.RCKRPIIAt GGExcFive ∧ RCKRowK2IIIAtTwoRemaining

end CFSG.StandardType.RCKC1
