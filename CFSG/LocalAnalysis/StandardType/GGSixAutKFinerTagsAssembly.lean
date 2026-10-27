module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsSp
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsSU
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsOmega
public import CFSG.LocalAnalysis.StandardType.GGAssemblySevenDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerLastAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Assembly

theorem ggLayerNotDFourTwoRound7_of_exc (hF4 : GGLayerNotDFourTwoTag .F4)
    (hE6 : GGLayerNotDFourTwoTag .E6) (hE7 : GGLayerNotDFourTwoTag .E7)
    (hE8 : GGLayerNotDFourTwoTag .E8) (hTwE6 : GGLayerNotDFourTwoTag .twistedE6) :
    GGLayerNotDFourTwoRound7 :=
  ⟨ggLayerNotDFourTwoTag_PSU, ggLayerNotDFourTwoTag_PSp, ggLayerNotDFourTwoTag_POmegaPlus,
    ggLayerNotDFourTwoTag_POmegaMinus, hF4, hE6, hE7, hE8, hTwE6⟩

theorem ggLayerNotDFourTwoInput_of_exc (hF4 : GGLayerNotDFourTwoTag .F4)
    (hE6 : GGLayerNotDFourTwoTag .E6) (hE7 : GGLayerNotDFourTwoTag .E7)
    (hE8 : GGLayerNotDFourTwoTag .E8) (hTwE6 : GGLayerNotDFourTwoTag .twistedE6) :
    GGLayerNotDFourTwoInput :=
  ggLayerNotDFourTwoInput_of_remaining ggLayerNotDFourTwoTag_PSU ggLayerNotDFourTwoTag_PSp
    ggLayerNotDFourTwoTag_POmegaPlus ggLayerNotDFourTwoTag_POmegaMinus hF4 hE6 hE7 hE8 hTwE6

theorem ggLayerNotUFourAltSixRest_of_exc (hF4 : GGLayerNotUFourAltSixTag .F4)
    (hE6 : GGLayerNotUFourAltSixTag .E6) (hE7 : GGLayerNotUFourAltSixTag .E7)
    (hE8 : GGLayerNotUFourAltSixTag .E8) (hTwE6 : GGLayerNotUFourAltSixTag .twistedE6) :
    GGLayerNotUFourAltSixRest :=
  ⟨ggLayerNotUFourAltSixTag_PSU, ggLayerNotUFourAltSixTag_PSp,
    ggLayerNotUFourAltSixTag_POmegaPlus, ggLayerNotUFourAltSixTag_POmegaMinus, hF4, hE6, hE7, hE8,
    hTwE6⟩

theorem ggStepTwoAutKRestInput_of_last_exc (h3 : GGAutKCanonIIIInput)
    (h4 : GGAutKCanonIVInput) (hF : GGSixFieldFiveInput)
    (dF4 : GGLayerNotDFourTwoTag .F4) (dE6 : GGLayerNotDFourTwoTag .E6)
    (dE7 : GGLayerNotDFourTwoTag .E7) (dE8 : GGLayerNotDFourTwoTag .E8)
    (dTwE6 : GGLayerNotDFourTwoTag .twistedE6) (uF4 : GGLayerNotUFourAltSixTag .F4)
    (uE6 : GGLayerNotUFourAltSixTag .E6) (uE7 : GGLayerNotUFourAltSixTag .E7)
    (uE8 : GGLayerNotUFourAltSixTag .E8) (uTwE6 : GGLayerNotUFourAltSixTag .twistedE6)
    (h2 : GGStepTwoChoiceThreeTwoRest) : GGStepTwoAutKRestInput :=
  ggStepTwoAutKRestInput_of_last h3 h4 hF (ggLayerNotDFourTwoRound7_of_exc dF4 dE6 dE7 dE8 dTwE6)
    (ggLayerNotUFourAltSixRest_of_exc uF4 uE6 uE7 uE8 uTwE6) h2

end Assembly

end CFSG.StandardType
