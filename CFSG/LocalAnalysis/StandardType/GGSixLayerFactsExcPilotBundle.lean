module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotNonsplit
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Layer

@[expose] def GGLayerTagsPilotRest : Prop :=
  GGExcAdjCoreNonToralRestInput .F4 ∧
    (GGWeylFamQuotSolvInput .E7 ∧ GGExcAdjCoreNonToralRestInput .E7) ∧
    (GGWeylFamQuotSolvInput .E8 ∧ GGExcAdjCoreNonToralRestInput .E8) ∧
    (GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6) ∧
    (GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6)

theorem ggLayerTagsRound5_of_pilotRest (h : GGLayerTagsPilotRest) : GGLayerTagsRound5 :=
  ⟨ggExcAdjCoreRestInput_F4_of_nonToral (ggExcAdjCoreNonToralInput_of_rest_F4 h.1),
    ggExcAdjCoreRestInput_of_nonToral h.2.1.1 (ggExcAdjCoreNonToralInput_of_rest_E7 h.2.1.2),
    ggExcAdjCoreRestInput_of_nonToral h.2.2.1.1 (ggExcAdjCoreNonToralInput_of_rest_E8 h.2.2.1.2),
    h.2.2.2.1, h.2.2.2.2⟩

theorem ggLayerInputs_of_pilotRest (h : GGLayerTagsPilotRest) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_round5 (ggLayerTagsRound5_of_pilotRest h)

end Layer

end CFSG.StandardType
