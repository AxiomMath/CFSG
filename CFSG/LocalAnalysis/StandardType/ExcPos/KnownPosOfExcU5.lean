module

public import CFSG.LocalAnalysis.StandardType.ExcPos.Assembly
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1a
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairOneHolds
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcURHolds
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7Holds
public import CFSG.LocalAnalysis.StandardType.ExcPos.OrdinaryNeighbour
public import CFSG.LocalAnalysis.StandardType.ExcPos.OrdinaryNeighbourPinned
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcPosRange
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcNoF4NoPSUPSpNoPOmegaDefs

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType


theorem ggSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmega_of_excU5 (hU5 : ExcU5) :
    GGSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmega := by
  have hE : ∀ t : StatedLieTag, (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
      GGSixExcPosExplicit t := fun t ht =>
    ggSixExcPosExplicit_of_units excU1a excU1b_holds excUR_holds hU5 excU7_holds ht
  exact ⟨ggSixLieKnownPos_E6_of_explicit (hE _ (Or.inl rfl)),
    ggSixLieKnownPos_E7_of_explicit (hE _ (Or.inr (Or.inl rfl))),
    ggSixLieKnownPos_E8_of_explicit (hE _ (Or.inr (Or.inr (Or.inl rfl)))),
    ggSixLieKnownPos_twistedE6_of_explicit (hE _ (Or.inr (Or.inr (Or.inr rfl))))⟩

theorem ggSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmega_of_pairADE
    (hPair : RCKRP.RCKCarrierPairADE) : GGSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmega :=
  ggSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmega_of_excU5
    (excU5_of_pinned (excU5Pinned_of_pieces hPair))

end CFSG.StandardType.LieKnownR2.ExcPos

end
