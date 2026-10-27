module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssembly
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.StandardType

open CFSG.ComponentClassification

theorem ggLBalanceInput_of_catalogueSchreier (hS : CatalogueRelativeB.CatalogueSchreier) :
    GGLBalanceInput :=
  fun X _ _ hK p hp P hP => (LBalance.l_balance_clauses hS X hK p hp P hP).2

theorem ggNbrSubcomponentInput_of_catalogueSchreier (hS : CatalogueRelativeB.CatalogueSchreier)
    (hP : GGStdSubPrimeInput) : GGNbrSubcomponentInput :=
  ggNbrSubcomponentInput_of_lBalance (ggLBalanceInput_of_catalogueSchreier hS) hP

theorem ggNbrSubcomponentInput_of_catalogueSchreier_small
    (hS : CatalogueRelativeB.CatalogueSchreier) (hB : GGBstarInput) (hs : GGStdSubSmallInput) :
    GGNbrSubcomponentInput :=
  ggNbrSubcomponentInput_of_small (ggLBalanceInput_of_catalogueSchreier hS) hB hs

theorem ggFieldNbrCanonicalInput_of_catalogueSchreier
    (hS : CatalogueRelativeB.CatalogueSchreier) (h4 : GGFieldNbrInnerInput)
    (hs : GGStdSubSmallInput) : GGFieldNbrCanonicalInput :=
  ggFieldNbrCanonicalInput_of_lBalance (ggLBalanceInput_of_catalogueSchreier hS) h4 hs

end CFSG.StandardType

end
