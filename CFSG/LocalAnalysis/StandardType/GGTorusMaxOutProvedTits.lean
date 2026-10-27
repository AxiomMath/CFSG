module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_tits
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨e⟩ := e
  apply CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd
  rw [CFSG.AGLEmbeddingD2.card_outer_tits_of_mulEquiv d hd e, hd, tmLieOut]

end CFSG.StandardType.FrameRoute
