module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEBundle
public import CFSG.LocalAnalysis.StandardType.GGAssemblyNineDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Assembly

theorem ggLayerNotExcThreeTag_F4_of_inputs (hS : GGExcSmallCompOrderInput)
    (hN : GGExcCentCompNonToralInput .F4) : GGLayerNotExcThreeTag .F4 :=
  ggLayerNotExcThreeTag_F4_of_cent fun _ _ _ _ hK4 =>
    ggCentCompNotExcThree_of_inputs ggWeylFamQuotSolvInput_F4 hS hN hK4

theorem ggLayerNotExcThreeTag_E8_of_inputs (hW : GGWeylFamQuotSolvInput .E8)
    (hS : GGExcSmallCompOrderInput) (hN : GGExcCentCompNonToralInput .E8) :
    GGLayerNotExcThreeTag .E8 :=
  ggLayerNotExcThreeTag_E8_of_cent fun _ _ _ _ hK4 =>
    ggCentCompNotExcThree_of_inputs hW hS hN hK4

theorem ggLayerNotExcThreeTag_E7_of_inputs (hW : GGWeylFamQuotSolvInput .E7)
    (hS : GGExcSmallCompOrderInput) (hN : GGExcCentCompNonToralInput .E7) :
    GGLayerNotExcThreeTag .E7 :=
  ggLayerNotExcThreeTag_E7_of_cent fun _ _ _ _ hK4 =>
    ggCentCompNotExcThree_of_inputs hW hS hN hK4

end Assembly

section Rest

@[expose] def GGLayerNotExcThreeRest : Prop :=
  GGExcSmallCompOrderInput ∧ GGExcCentCompNonToralInput .F4 ∧ GGExcCentCompNonToralInput .E7 ∧
    GGExcCentCompNonToralInput .E8 ∧ GGE6InndiagCompNonToralInput ∧ GGTwE6InndiagCompInput

theorem ggLayerNotExcThreeTags_of_rest (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerNotExcThreeRest) :
    GGLayerNotExcThreeTag .F4 ∧ GGLayerNotExcThreeTag .E6 ∧ GGLayerNotExcThreeTag .E7 ∧
      GGLayerNotExcThreeTag .E8 ∧ GGLayerNotExcThreeTag .twistedE6 := by
  obtain ⟨-, ⟨hW7, -⟩, ⟨hW8, -⟩, ⟨hW6, hR6⟩, hRT⟩ := hlay
  obtain ⟨hS, hN4, hN7, hN8, hN6, hNT⟩ := h
  exact ⟨ggLayerNotExcThreeTag_F4_of_inputs hS hN4,
    ggLayerNotExcThreeTag_E6_of_inputs hW6
      (ggE6InndiagCoreInput_of_nonToral hW6 (ggE6InndiagCoreNonToralInput_of_rest hR6)) hS hN6,
    ggLayerNotExcThreeTag_E7_of_inputs hW7 hS hN7, ggLayerNotExcThreeTag_E8_of_inputs hW8 hS hN8,
    ggLayerNotExcThreeTag_twistedE6_of_inputs (ggTwE6InndiagCoreInput_of_rest hRT) hNT⟩

theorem ggLayerNotDFourTwoRound9_of_excRest (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerNotExcThreeRest) : GGLayerNotDFourTwoRound9 := by
  obtain ⟨h4, h6, h7, h8, hT⟩ := ggLayerNotExcThreeTags_of_rest hlay h
  exact ⟨ggLayerNotDFourTwoTag_of_notExcThree h4, ggLayerNotDFourTwoTag_of_notExcThree h6,
    ggLayerNotDFourTwoTag_of_notExcThree h7, ggLayerNotDFourTwoTag_of_notExcThree h8,
    ggLayerNotDFourTwoTag_of_notExcThree hT⟩

theorem ggLayerNotUFourAltSixRound9_of_excRest (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerNotExcThreeRest) : GGLayerNotUFourAltSixRound9 := by
  obtain ⟨h4, h6, h7, h8, hT⟩ := ggLayerNotExcThreeTags_of_rest hlay h
  exact ⟨ggLayerNotUFourAltSixTag_of_notExcThree h4, ggLayerNotUFourAltSixTag_of_notExcThree h6,
    ggLayerNotUFourAltSixTag_of_notExcThree h7, ggLayerNotUFourAltSixTag_of_notExcThree h8,
    ggLayerNotUFourAltSixTag_of_notExcThree hT⟩

end Rest

end CFSG.StandardType
