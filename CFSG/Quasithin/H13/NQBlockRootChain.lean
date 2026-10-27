module

public import CFSG.Quasithin.H13.NQBlockPrimeLinearThree
public import CFSG.Quasithin.H13.NQBlockLayerResidual

public section

namespace CFSG.Quasithin.H13.NQBlock

theorem stmtQuasisimpleAmbientOneRankTwoPrime_of_catalog
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hI : ∀ (F : Type) [Field F] [Finite F], NQCat.OddLinearThreeInvolutionSylowStructure F) :
    StmtQuasisimpleAmbientOneRankTwoPrime :=
  stmtQuasisimpleAmbientOneRankTwoPrime_of hCat (primeLinearThreeAmbientPrime_of hI)

theorem stmtTwoPrimeCaptureConfinesCharNormalizer_of_catalog
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hI : ∀ (F : Type) [Field F] [Finite F], NQCat.OddLinearThreeInvolutionSylowStructure F) :
    StmtTwoPrimeCaptureConfinesCharNormalizer :=
  stmtTwoPrimeCaptureConfinesCharNormalizer_of sqtkCLayerPerfectResidual_proved
    (stmtQuasisimpleAmbientOneRankTwoPrime_of_catalog hCat hI)

theorem stmtOriginalRadicalNormalizerCoreControl_of_catalog
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hI : ∀ (F : Type) [Field F] [Finite F], NQCat.OddLinearThreeInvolutionSylowStructure F) :
    StmtOriginalRadicalNormalizerCoreControl :=
  stmtOriginalRadicalNormalizerCoreControl_of sqtkCLayerPerfectResidual_proved
    (stmtQuasisimpleAmbientOneRankTwoPrime_of_catalog hCat hI)

theorem stmtCharNormalizersConfined_of_catalog
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hI : ∀ (F : Type) [Field F] [Finite F], NQCat.OddLinearThreeInvolutionSylowStructure F) :
    StmtCharNormalizersConfined :=
  stmtCharNormalizersConfined_of sqtkCLayerPerfectResidual_proved hCat
    (primeLinearThreeAmbientPlane_of hI)

theorem stmtEveryOriginalRadicalCharNormalizerConfined_of_catalog
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hI : ∀ (F : Type) [Field F] [Finite F], NQCat.OddLinearThreeInvolutionSylowStructure F) :
    StmtEveryOriginalRadicalCharNormalizerConfined :=
  stmtEveryOriginalRadicalCharNormalizerConfined_of sqtkCLayerPerfectResidual_proved
    (stmtQuasisimpleAmbientOneRankTwoPrime_of_catalog hCat hI) hCat
    (primeLinearThreeAmbientPlane_of hI)

end CFSG.Quasithin.H13.NQBlock
