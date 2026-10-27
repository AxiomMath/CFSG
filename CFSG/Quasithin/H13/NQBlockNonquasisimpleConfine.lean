module

public import CFSG.Quasithin.H13.NQBlockRadicalEscapeHolds
public import CFSG.Quasithin.H13.NQCoreUniversalConfine
public import CFSG.Quasithin.H13.NQCoreSChainOrbits
public import CFSG.Quasithin.H13.NQCoreSChainNormal
public import CFSG.Quasithin.H13.NQCoreSChainPair
public import CFSG.Quasithin.H13.NQCoreAtLeastTwoNoncentral
public import CFSG.Quasithin.H13.NQBlockContainingLocals

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

@[expose] def OriginalKNonquasisimpleConfinement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ D : Subgroup G, quasithinIsMaximalLocal T D → quasithinIsFaithfulLocal T D →
      nqOriginalK T L ≤ D → ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D) →
        D = L ∧ normalizer (D : Set G) = M ∧ D ≤ M

variable {G : Type} [Group G] [Finite G]

theorem eq_of_maximalLocal_le
    {T L M D : Subgroup G} (h : QTNQ T L M) (hD : quasithinIsMaximalLocal T D)
    (hTD : T ≤ normalizer (D : Set G)) (hDM : D ≤ M) (hKD : nqOriginalK T L ≤ D) : D = L := by
  classical
  have := h.simple
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
  obtain ⟨hKf, -⟩ := original_common_residual_is_faithful_and_has_exact_reduced_action_kernel h hR
  obtain ⟨hKL, -⟩ := original_K_quotient_facts h
  have hO2M := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal h.max_two_local.1
  have hTsM := isSylowTwoOf_of_qtnq h h.t_le
  have hcomp : ∀ D' : Subgroup G, quasithinIsMaximalLocal T D' → T ≤ normalizer (D' : Set G) →
      D' ≤ M → D' ∈ cComp M := by
    intro D' hD' hTD' hD'M
    obtain ⟨D₀, ⟨hD₀, -⟩, -, -, hmax⟩ := sylowNormalizedLocalNormalComponent_proved G
      h.nonabelian h.qtke M T D' hO2M hTsM hD'M hD'.1 hTD'
    obtain ⟨hD₀D, -⟩ := hmax hD'
    rwa [hD₀D] at hD₀
  obtain ⟨C, -, hCu⟩ := QuasithinUnique.Vol2Native.existsUnique_cComp_ge_of_isLocal h.nonabelian
    h.qtke hO2M hTsM (hKL.trans h.l_le) hKf.1
  exact (hCu D ⟨hcomp D hD hTD hDM, hKD⟩).trans (hCu L ⟨hcomp L h.maximal_local
    (h.eq_normalizer ▸ h.t_le) h.l_le, hKL⟩).symm

theorem originalKNonquasisimpleConfinement_holds :
    OriginalKNonquasisimpleConfinement := by
  intro G _ _ T L M h D hDmax hDf hKD hDq
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
  have hTD := (containing_local_facts h hR hDmax.1 hKD).1
  have hA7u := NQCore.sylowNormalizedMaximalLocalUniqueNormalizer_of
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved Vol2.Ch10.SecA.a38ForSQTKCat_proved
    QuasithinUnique.Vol2Native.a39ForSQTKCat_proved
  have hO := NQCore.sylow_normalized_prime_residual_nonnormal_overgroup_component_orbits
    NQRigid.stmtEscapingComponentAction_holds NQRigid.stmtOuterRankContainment_holds
    NQRigid.stmtPairContainment_holds NQCat.stmtOuterDerivedCoprime_holds
    NQRigid.factCenterOddPart_holds NQRigid.factOuterPrime_holds
    NQRigid.factThinCentralQuotient_holds QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
  have hN := NQCore.sylow_normalized_prime_residual_normal_component_exclusion
    stmtTwoPrimeCaptureConfinesCharNormalizer_holds stmtCharNormalizersConfined_holds
    NQRigid.factCenterOddPart_holds NQRigid.factSimpleQuotientSQT_holds
    (QTESylow.catalog_noncyclic_prime_sylow_product_model_restriction
        QTESylow.he_ru_noncyclic_prime_sylow_product) NQRigid.stmtNoncyclicLocalSylowFourEven_holds
    NQRigid.stmtCPUOffenderSection_holds NQRigid.stmtJ4SingleComponent_holds
    NQRigid.stmtTitsSylowProduct_holds
  have hP := NQCore.sylow_normalized_prime_residual_paired_component_exclusion
    stmtTwoPrimeCaptureConfinesCharNormalizer_holds stmtCharNormalizersConfined_holds
    NQRigid.factCenterOddPart_holds NQRigid.factSimpleQuotientSQT_holds
    NQRigid.factQuadraticOffender_holds NQRigid.stmtCPUOffenderSection_holds
    NQRigid.stmtCPUShortBlock_holds
  have hI := NQCore.stmtIntrinsicActionExclusion_of_inputs hA7u
    sylowNormalizedLocalNormalComponent_proved stmtOriginalWitnessSingleton_holds
  obtain ⟨hDM, hND, -⟩ := NQCore.every_sylow_normalized_maximal_nonquasisimple_local_is_confined
    hA7u sylowNormalizedLocalNormalComponent_proved hO hN hP hI h hDmax hDf hTD hDq
  exact ⟨eq_of_maximalLocal_le h hDmax hTD hDM hKD, hND, hDM⟩

theorem originalKContainingConfinement_of_confinement
    (hconf : OriginalKNonquasisimpleConfinement) (h1323 : Stmt13_1_2_three) :
    OriginalKContainingConfinement := by
  intro G _ _ T L M h H hH hKTH hHM A hA hKA hAu hY C hC
  classical
  by_cases hCA : C = A
  · subst hCA
    obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
    have hTH : T ≤ H := le_sup_right.trans hKTH
    have hAloc : quasithinIsLocal T C := QuasithinUnique.Vol2Native.isLocal_of_mem_cComp
      (CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hH.1) (isSylowTwoOf_of_qtnq h hTH) hC
    obtain ⟨A', hA'm, hCA'⟩ := exists_maximalLocal_ge hAloc
    have hKA' : nqOriginalK T L ≤ A' := hKA.trans hCA'
    have hf := containing_local_facts h hR hA'm.1 hKA'
    have hA'f : quasithinIsFaithfulLocal T A' := hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    by_contra hCM
    have hA'M : ¬ A' ≤ M := fun h' => hCM (hCA'.trans h')
    have hq : CFSG.IsQuasisimple (↥A' ⧸ CFSG.pCore 2 ↥A') := by
      by_contra hq
      exact hA'M (hconf G T L M h A' hA'm hA'f hKA' hq).2.2
    exact not_qt13Five_of_maximalLocal h hA'm hKA' hf.1
      (h1323 G T A' h.simple h.nonabelian h.qtke h.sylow h.not_excluded hA'm hA'f hq)
  · exact (le_sSup ⟨hC, hCA⟩ : C ≤ nqComplementaryLayer H A).trans hY

end CFSG.Quasithin.H13.NQBlock
