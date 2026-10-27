module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcNonsplit
public import CFSG.LocalAnalysis.StandardType.GGAssemblySixDefs

public section

namespace CFSG.StandardType

section Round

@[expose] def GGLayerPDivExcRest : Prop :=
  GGExcPDivNonToralRestInput .F4 ∧ GGE6PDivNonToralRestInput ∧ GGExcPDivNonToralRestInput .E7 ∧
    GGExcPDivNonToralRestInput .E8 ∧ GGTwE6PDivInput

theorem ggLayerPDivRound6_of_excRest (hlay : GGLayerTagsPilotRestSix) (h : GGLayerPDivExcRest) :
    GGLayerPDivRound6 :=
  ⟨ggLayerPDivTag_F4_of_nonToral (ggExcPDivNonToralInput_of_rest_F4 h.1),
    ggLayerPDivTag_E6_of_nonToral hlay.2.2.2.1.1 (ggE6PDivNonToralInput_of_rest h.2.1),
    ggLayerPDivTag_E7_of_nonToral hlay.2.1.1 (ggExcPDivNonToralInput_of_rest_E7 h.2.2.1),
    ggLayerPDivTag_E8_of_nonToral hlay.2.2.1.1 (ggExcPDivNonToralInput_of_rest_E8 h.2.2.2.1),
    ggLayerPDivTag_twistedE6_of_input h.2.2.2.2⟩

end Round

end CFSG.StandardType
