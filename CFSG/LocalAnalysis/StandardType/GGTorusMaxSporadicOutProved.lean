module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicMultD1CenterNineOut

public section

namespace CFSG.StandardType.FrameRoute

theorem tmSporadicOutInput_proved :
    TmSporadicOutInput := by
  intro s J _ _ ⟨e⟩
  have h := CFSG.AGLEmbedding.SporadicMultD1.card_outer_sporadic_dvd_two
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  rw [← Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv] at h
  exact CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd h

end CFSG.StandardType.FrameRoute

end
