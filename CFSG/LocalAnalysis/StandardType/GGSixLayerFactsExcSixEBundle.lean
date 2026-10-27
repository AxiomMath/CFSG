module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotBundle
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixENonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwistedNonsplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Layer

@[expose] def GGLayerTagsPilotRestSix : Prop :=
  GGExcAdjCoreNonToralRestInput .F4 ∧
    (GGWeylFamQuotSolvInput .E7 ∧ GGExcAdjCoreNonToralRestInput .E7) ∧
    (GGWeylFamQuotSolvInput .E8 ∧ GGExcAdjCoreNonToralRestInput .E8) ∧
    (GGWeylFamQuotSolvInput .E6 ∧ GGE6InndiagCoreNonToralRestInput) ∧
    GGTwE6InndiagCoreRestInput

theorem ggLayerTagsPilotRest_of_six (h : GGLayerTagsPilotRestSix) : GGLayerTagsPilotRest :=
  ⟨h.1, h.2.1, h.2.2.1, ggLayerTags_E6_of_rest h.2.2.2.1.1 h.2.2.2.1.2,
    ggLayerTags_twistedE6_of_rest h.2.2.2.2⟩

theorem ggLayerTagsRound5_of_six (h : GGLayerTagsPilotRestSix) : GGLayerTagsRound5 :=
  ggLayerTagsRound5_of_pilotRest (ggLayerTagsPilotRest_of_six h)

theorem ggLayerInputs_of_six (h : GGLayerTagsPilotRestSix) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_pilotRest (ggLayerTagsPilotRest_of_six h)

end Layer

end CFSG.StandardType
