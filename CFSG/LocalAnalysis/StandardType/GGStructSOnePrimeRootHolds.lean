module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootPSL
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootPSU
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootPSp
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootOmega
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TLayer

public section

namespace CFSG.StandardType

theorem ggStructSOnePrimeRoot_holds : GGStructSOnePrimeRoot :=
  ggStructSOnePrimeRoot_of_tagInputs CFSG.LocalAnalysis.GLTheoremA.I142T.layerFixTyped_holds
    ggRootInvolCentTypedTag_PSL ggRootInvolCentTypedTag_PSU ggRootInvolCentTypedTag_PSp
    ggRootInvolCentTypedTag_POmegaPlus ggRootInvolCentTypedTag_POmegaMinus
    (ggRootInvolCentTypedTag_of_modelTyped ggRootInvolModelTypedTag_F4)
    (ggRootInvolCentTypedTag_of_modelTyped ggRootInvolModelTypedTag_E6)
    (ggRootInvolCentTypedTag_of_modelTyped ggRootInvolModelTypedTag_E7)
    (ggRootInvolCentTypedTag_of_modelTyped ggRootInvolModelTypedTag_E8)
    (ggRootInvolCentTypedTag_of_modelTyped ggRootInvolModelTypedTag_twistedE6)

end CFSG.StandardType
