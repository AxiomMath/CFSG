module

public import CFSG.Quasithin.H13.NQBlockXTOrbitPlacement
public import CFSG.Quasithin.H13.NQCatOddLinearThreeHolds
public import CFSG.Quasithin.H13.QTESylowRoot
public import CFSG.Quasithin.H13.QTESylowHeRu

public section

namespace CFSG.Quasithin.H13.NQBlock

theorem stmtTwoPrimeCaptureConfinesCharNormalizer_holds
    : StmtTwoPrimeCaptureConfinesCharNormalizer :=
  stmtTwoPrimeCaptureConfinesCharNormalizer_of_catalog
    (QTESylow.catalog_noncyclic_prime_sylow_product_model_restriction
        QTESylow.he_ru_noncyclic_prime_sylow_product)
    fun _ _ _ => NQCat.oddLinearThreeInvolutionSylowStructure_holds

theorem stmtCharNormalizersConfined_holds
    : StmtCharNormalizersConfined :=
  stmtCharNormalizersConfined_of_catalog (QTESylow.catalog_noncyclic_prime_sylow_product_model_restriction
      QTESylow.he_ru_noncyclic_prime_sylow_product)
    fun _ _ _ => NQCat.oddLinearThreeInvolutionSylowStructure_holds

theorem originalXTOrbitPlacement_of_outerDerivedCoprime
    (hOD : NQRigid.StmtOuterDerivedCoprime) : OriginalXTOrbitPlacement :=
  original_XT_orbit_placement_of (QTESylow.catalog_noncyclic_prime_sylow_product_model_restriction
      QTESylow.he_ru_noncyclic_prime_sylow_product)
    (fun _ _ _ => NQCat.oddLinearThreeInvolutionSylowStructure_holds) hOD

end CFSG.Quasithin.H13.NQBlock
