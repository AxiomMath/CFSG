module

public import CFSG.Quasithin.H13.NQRigidAssembly
public import CFSG.Quasithin.H13.NQRigidB4
public import CFSG.Quasithin.H13.NQRigidR1
public import CFSG.Quasithin.H13.NQRigidOverlap
public import CFSG.Quasithin.H13.NQRigidAnother
public import CFSG.Quasithin.H13.NQBlockRootHolds

public section

namespace CFSG.Quasithin.H13.NQRigid

open CFSG.Open CFSG.QuasithinUnique

theorem oblRigidWholeModule_of_open
    (h56 : AsB56) (h317 : Theorem317Statement)
    (h3 : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G)
    (hS : NQBlock.OriginalKEscapingSourceY) (hE : NQBlock.OriginalNoNormalSourceYEscapes) :
    OblRigidWholeModule :=
  oblRigidWholeModule_of_inputs h56 h317 (stmtAnotherMaximalTwoLocal_of_modelReduction h3) hS hE
      (stmtOverlapNormalizesOriginalK_of_singleton NQBlock.factWitnessSingleton_holds)

theorem nonquasisimpleInternalCentralizerRigidity_of_open
    (h56 : AsB56) (h317 : Theorem317Statement)
    (h3 : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G)
    (hS : NQBlock.OriginalKEscapingSourceY) (hE : NQBlock.OriginalNoNormalSourceYEscapes)
    (hR2a : OblRigidCPUEvenLinearThreeParabolic) (hR2b : OblRigidCPUSymplecticFourDeleted) :
    NQBlock.NonquasisimpleInternalCentralizerRigidity :=
  nonquasisimpleInternalCentralizerRigidity_of_facts
      (factWitnessSingleton_of_inputs
          (NQBlock.originalXTNormalComponent_of
              (NQBlock.originalXTPlacement_of_groupCPU
                  (NQBlock.originalXTOrbitPlacement_of_outerDerivedCoprime
                      NQCat.stmtOuterDerivedCoprime_holds) stmtCPUOffenderSection_holds
                  stmtCPUShortBlock_holds)
              (NQBlock.cpuOffenderSection_of stmtCPUOffenderSection_holds)
              (QTESylow.catalog_noncyclic_prime_sylow_product_model_restriction
                  QTESylow.he_ru_noncyclic_prime_sylow_product))
          NQBlock.originalWitnessExcludesCrossLinearThree
          NQBlock.originalWitnessExcludesEvenSymplecticFour_holds) factCenterOddPart_holds
      factOuterPrime_holds factSimpleQuotientSQT_holds factNonscalarG2Triality_holds
      factLargeRee_holds factThinCentralQuotient_holds factQuadraticOffender_holds
      (QTESylow.catalog_noncyclic_prime_sylow_product_model_restriction
          QTESylow.he_ru_noncyclic_prime_sylow_product) stmtEscapingComponentAction_holds
      stmtOuterRankContainment_holds stmtPairContainment_holds stmtOrdinaryEvenSymplecticFour_holds
      stmtNoncyclicLocalSylowFourEven_holds stmtFourDivisibilityFields_holds
      stmtCPUOffenderSection_holds stmtCPUShortBlock_holds stmtJ4SingleComponent_holds
      stmtTitsSylowProduct_holds NQCat.stmtOuterDerivedCoprime_holds
      (oblRigidWholeModule_of_open h56 h317 h3 hS hE) hR2a hR2b

end CFSG.Quasithin.H13.NQRigid
