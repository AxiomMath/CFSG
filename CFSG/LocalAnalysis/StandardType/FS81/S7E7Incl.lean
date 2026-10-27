module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1

section E7Model


@[expose] noncomputable def zmodTwoEquivGalois : ZMod 2 ≃+* GaloisField 2 1 :=
  letI := Fintype.ofFinite (GaloisField 2 1)
  FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, natCard_galoisField_two_one])

@[expose] noncomputable def e7Incl : ↥(adjointGroup .E7 (ZMod 2)) →* ↥(adjointGroup .E8 GF₂) :=
  (E8Pilot.e7Levi GF₂).subtype.comp
    ((E8Pilot.e7LeviEquiv GF₂).symm.toMonoidHom.comp
      (E8Pilot.adjointGroupE7RingEquiv zmodTwoEquivGalois).toMonoidHom)

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
