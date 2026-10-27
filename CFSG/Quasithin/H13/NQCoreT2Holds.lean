module

public import CFSG.Quasithin.H13.NQCoreT2Assembly
public import CFSG.Quasithin.H13.NQCoreAtLeastTwoNoncentral
public import CFSG.Quasithin.H13.NQCoreWitness
public import CFSG.Quasithin.H13.NQCoreSChainNormal
public import CFSG.Quasithin.H13.NQCoreSChainPair
public import CFSG.Quasithin.H13.NQCoreHYRigid
public import CFSG.Quasithin.H13.NQBlockRadicalEscapeHolds
public import CFSG.Quasithin.H13.LocDblSporadic
public import CFSG.Quasithin.H13.NQBlockFiveOrders
public import CFSG.Quasithin.H13.NQCoreT2Rank
public import CFSG.Quasithin.H13.NQCoreSChainOrbits

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem sylowNormalizedMaximalLocalUniqueNormalizer_holds :
    U3.SylowNormalizedMaximalLocalUniqueNormalizer :=
  sylowNormalizedMaximalLocalUniqueNormalizer_of Vol2Native.a37ForSQTKCat_proved
    (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
    Vol2Native.a39ForSQTKCat_proved

theorem stmtSCComponentOrbits_holds :
    StmtSCComponentOrbits :=
  sylow_normalized_prime_residual_nonnormal_overgroup_component_orbits
    NQRigid.stmtEscapingComponentAction_holds NQRigid.stmtOuterRankContainment_holds
    NQRigid.stmtPairContainment_holds NQCat.stmtOuterDerivedCoprime_holds
    NQRigid.factCenterOddPart_holds NQRigid.factOuterPrime_holds
    NQRigid.factThinCentralQuotient_holds Vol2Native.a36CoreForSQTKCat_proved

theorem stmtSCNormalExclusion_holds :
    StmtSCNormalExclusion :=
  sylow_normalized_prime_residual_normal_component_exclusion
    NQBlock.stmtTwoPrimeCaptureConfinesCharNormalizer_holds
    NQBlock.stmtCharNormalizersConfined_holds NQRigid.factCenterOddPart_holds
    NQRigid.factSimpleQuotientSQT_holds (QTESylow.catalog_noncyclic_prime_sylow_product_model_restriction
        QTESylow.he_ru_noncyclic_prime_sylow_product)
    NQRigid.stmtNoncyclicLocalSylowFourEven_holds NQRigid.stmtCPUOffenderSection_holds
    NQRigid.stmtJ4SingleComponent_holds NQRigid.stmtTitsSylowProduct_holds

theorem stmtSCPairedExclusion_holds :
    StmtSCPairedExclusion :=
  sylow_normalized_prime_residual_paired_component_exclusion
    NQBlock.stmtTwoPrimeCaptureConfinesCharNormalizer_holds
    NQBlock.stmtCharNormalizersConfined_holds NQRigid.factCenterOddPart_holds
    NQRigid.factSimpleQuotientSQT_holds NQRigid.factQuadraticOffender_holds
    NQRigid.stmtCPUOffenderSection_holds NQRigid.stmtCPUShortBlock_holds

theorem stmtIntrinsicActionExclusion_holds :
    StmtIntrinsicActionExclusion :=
  stmtIntrinsicActionExclusion_of_inputs sylowNormalizedMaximalLocalUniqueNormalizer_holds
    NQBlock.sylowNormalizedLocalNormalComponent_proved NQBlock.stmtOriginalWitnessSingleton_holds

theorem every_sylow_normalized_maximal_nonquasisimple_local_is_confined_holds
    {G : Type} [Group G] [Finite G] {T L M D : Subgroup G} (h : QTNQ T L M)
    (hDmax : quasithinIsMaximalLocal T D) (hDf : quasithinIsFaithfulLocal T D)
    (hTD : T ≤ Subgroup.normalizer (D : Set G))
    (hDq : ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D)) :
    D ≤ M ∧ Subgroup.normalizer (D : Set G) = M ∧
      ∀ (p : ℕ) (X : Subgroup G), QTTMaxNQPrime T L M D p X →
        U3.UniqueMaxTwoLocal (X ⊔ T) M :=
  every_sylow_normalized_maximal_nonquasisimple_local_is_confined
    sylowNormalizedMaximalLocalUniqueNormalizer_holds
    NQBlock.sylowNormalizedLocalNormalComponent_proved stmtSCComponentOrbits_holds
    stmtSCNormalExclusion_holds stmtSCPairedExclusion_holds stmtIntrinsicActionExclusion_holds h
    hDmax hDf hTD hDq

theorem nonquasisimpleRadicalNormalizerWitness_of_open
    (h3214 : Stmt3_2_14) (h1323 : Stmt13_1_2_three) :
    NQBlock.NonquasisimpleRadicalNormalizerWitness :=
  nonquasisimpleRadicalNormalizerWitness_of Vol2Native.a37ForSQTKCat_proved
    (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
    Vol2Native.a39ForSQTKCat_proved NQBlock.sylowNormalizedLocalNormalComponent_proved h1323
    NQBlock.fiveQuotientExactOrders_holds
    stmtSCComponentOrbits_holds stmtSCNormalExclusion_holds stmtSCPairedExclusion_holds
    (snRadicalCentralizer Vol2Native.a36CoreForSQTKCat_proved h3214)

theorem nonquasisimpleTIEscapingResidual_of_open
    (h3 : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G)
    (h1323 : Stmt13_1_2_three) (hpair : StmtEscapingPairExcluded)
    (hrank : StmtEscapingSingleTwoRank) : NQBlock.NonquasisimpleTIEscapingResidual :=
  nonquasisimpleTIEscapingResidual_of h3 LocDbl.local_double_embedding_exclusion
    Vol2Native.a37ForSQTKCat_proved sylowNormalizedMaximalLocalUniqueNormalizer_holds
    NQBlock.sylowNormalizedLocalNormalComponent_proved stmtSCComponentOrbits_holds
    stmtSCNormalExclusion_holds stmtSCPairedExclusion_holds stmtIntrinsicActionExclusion_holds
    h1323 stmtFiveModelLocalChainRigid_holds hpair hrank

theorem nonquasisimpleTIEscapingResidual_of_pair
    (h3 : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G)
    (h1323 : Stmt13_1_2_three) (hpair : StmtEscapingPairExcluded) :
    NQBlock.NonquasisimpleTIEscapingResidual :=
  nonquasisimpleTIEscapingResidual_of_open h3 h1323 hpair stmtEscapingSingleTwoRank_holds

end CFSG.Quasithin.H13.NQCore
