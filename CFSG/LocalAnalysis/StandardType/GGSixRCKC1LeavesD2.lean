module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesD3
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIModel

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKK1II

@[expose] def RCKRowIIAtTriAll :
    Prop :=
  ∀ (F : Type) [Field F] [Finite F] (σ : F →+* F), TriField F σ 1 → RCKRowIIAtTri F σ

@[expose] def GGSixRootCommKnownLeavesD2 :
    Prop :=
  RCKRP.RCKIntrinsicRoot ∧ RCKRowIIAtTriAll ∧ RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧
    RCKK2NbrRootSubShort ∧ RCKK2FlagRootSub ∧ RCKK2NbrCollinear ∧ RCKRowK2 .III RCKPosShort ∧
    RCKRowK2 .IIp (RCKPosCent 96)

end CFSG.StandardType.RCKC1
