module

public import CFSG.Quasithin.H13.NQBlockContainingLocals
public import CFSG.Quasithin.H13.NQBlockRadicalFactorization
public import CFSG.Quasithin.H13.NQBlockLayerResidual
public import CFSG.Quasithin.H13.LocDblSporadic
public import CFSG.Quasithin.Background.B69E22Link

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

variable {G : Type} [Group G]

abbrev nqSylowCenterClosure (T H : Subgroup G) : Subgroup G :=
  sSup {X | ∃ h ∈ H, CFSG.conjugate (quasithinOmegaOneCenter T) h = X}

variable [Finite G]

theorem containing_component
    {T L M : Subgroup G} (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) {H : Subgroup G}
    (hH : quasithinIsMaxTwoLocal H) (hKTH : nqOriginalK T L ⊔ T ≤ H) :
    ∃ A ∈ cComp H, nqOriginalK T L ≤ A ∧ (∀ A' ∈ cComp H, nqOriginalK T L ≤ A' → A' = A) ∧
      (A.subgroupOf H).Normal ∧ quasithinIsFaithfulLocal T A ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 H), A⁆ ≤ H ∧
      ((⁅omegaOneCenterOf 2 (pCoreOf 2 H), A⁆ : Subgroup G).subgroupOf H).Normal ∧
      CFSG.IsElementaryAbelian 2 ↥⁅omegaOneCenterOf 2 (pCoreOf 2 H), A⁆ ∧
      ⁅omegaOneCenterOf 2 R, nqOriginalK T L⁆ ≤ ⁅omegaOneCenterOf 2 (pCoreOf 2 H), A⁆ ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 H), A⁆ ≤ ⁅omegaOneCenterOf 2 (pCoreOf 2 A), A⁆ ∧
      ⁅⁅omegaOneCenterOf 2 (pCoreOf 2 H), A⁆, A⁆ = ⁅omegaOneCenterOf 2 (pCoreOf 2 H), A⁆ ∧
      nqOriginalK T L ⊓ centralizer ((⁅omegaOneCenterOf 2 (pCoreOf 2 H), A⁆ : Subgroup G) : Set G) ≤
        pCoreOf 2 (nqOriginalK T L) ∧
      ∀ A' : Subgroup G, quasithinIsMaximalLocal T A' → A ≤ A' →
        quasithinIsFaithfulLocal T A' ∧ T ≤ normalizer (A' : Set G) ∧
        ¬ QT13Five (↥A' ⧸ CFSG.pCore 2 ↥A') ∧ (¬ A ≤ M → ¬ A' ≤ M) ∧ (A' ≤ H ↔ A' = A) := by
  classical
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKf, -⟩ := original_common_residual_is_faithful_and_has_exact_reduced_action_kernel h hR
  obtain ⟨-, hTK, -⟩ := original_K_quotient_facts h
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hKH : nqOriginalK T L ≤ H := le_sup_left.trans hKTH
  have hTs := isSylowTwoOf_of_qtnq h hTH
  have hO2 := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hH.1
  obtain ⟨A, ⟨hA, hKA⟩, huniq, hAn, -⟩ :=
    sylowNormalizedLocalNormalComponent_proved G h.nonabelian h.qtke H T (nqOriginalK T L) hO2 hTs
      hKH hKf.1 hTK
  have hAH : A ≤ H := le_of_mem_cComp hA
  have hAloc : quasithinIsLocal T A := QuasithinUnique.Vol2Native.isLocal_of_mem_cComp hO2 hTs hA
  have hAf := (containing_local_facts h hR hAloc hKA).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, hDW, hWV, -, hWE, hWn, hWel, hWW, -, hCQ, -, -⟩ :=
    containing_normal_facts h hR hTH hO2 hAH ((normal_subgroupOf_iff_le_normalizer hAH).mp hAn)
      (perfect_of_mem_cComp hA) hKA
  refine ⟨A, hA, hKA, fun A' hA' hKA' => huniq A' ⟨hA', hKA'⟩, hAn, hAf, hWE, hWn, hWel, hDW, hWV,
    hWW, hCQ, fun A' hA'm hAA' => ?_⟩
  have hfA' := containing_local_facts h hR hA'm.1 (hKA.trans hAA')
  refine ⟨hfA'.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hfA'.1,
    not_qt13Five_of_maximalLocal h hA'm (hKA.trans hAA') hfA'.1,
    fun hAM hA'M => hAM (hAA'.trans hA'M), fun hA'H => ?_, fun he => he ▸ hAH⟩
  obtain ⟨C, ⟨hC, hA'C⟩, -⟩ := QuasithinUnique.Vol2Native.existsUnique_cComp_ge_of_isLocal
    h.nonabelian h.qtke hO2 hTs hA'H hA'm.1
  have hCA : C = A := huniq C ⟨hC, hKA.trans (hAA'.trans hA'C)⟩
  exact le_antisymm (hCA ▸ hA'C) hAA'

theorem containing_sylow_closure
    {T L M : Subgroup G} (h : QTNQ T L M) {H A : Subgroup G} (hH : quasithinIsMaxTwoLocal H)
    (hTH : T ≤ H) :
    nqSylowCenterClosure T H ≤ H ∧
      CFSG.Quasithin.IsPrimeReduced 2 ((nqSylowCenterClosure T H).subgroupOf H) ∧
      quasithinOmegaOneCenter T ≤ nqSylowCenterClosure T H ∧
      nqSylowCenterClosure T H ≤ qtnqVc H ∧ qtnqVc H ≤ omegaOneCenterOf 2 (pCoreOf 2 H) ∧
      pCoreOf 2 H ≤ centralizer (nqSylowCenterClosure T H : Set G) ∧
      (∀ B ∈ cComp H, ¬ B ≤ M →
        ⁅quasithinOmegaOneCenter T, B⁆ ≠ ⊥ ∧ ⁅nqSylowCenterClosure T H, B⁆ ≠ ⊥ ∧
        quasithinIsFaithfulLocal T B ∧
        ∃ B' : Subgroup G, (quasithinIsMaximalLocal T B' ∧ quasithinIsFaithfulLocal T B') ∧
          B ≤ B' ∧ ¬ B' ≤ M) ∧
      (¬ nqComplementaryLayer H A ≤ M ↔ ∃ B ∈ cComp H, B ≠ A ∧ ¬ B ≤ M) := by
  classical
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  set U := nqSylowCenterClosure T H with hUdef
  have hTs := isSylowTwoOf_of_qtnq h hTH
  have hO2 := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hH.1
  have hH2 : QuasithinUnique.CharTwo H :=
    QuasithinUnique.charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot h.qtke.2.1
      (isSylowTwoOf_top_of_qtnq h) hTH hO2
  have hHc : CFSG.IsCharacteristicP 2 ↥H :=
    QuasithinUnique.EscapingLocal.isCharacteristicP_of_charTwo hH2
  have hT'2 : IsPGroup 2 ↥(T.subgroupOf H) := h.sylow.1.comap_subtype
  have hT'odd : ¬ 2 ∣ (T.subgroupOf H).index := hTs.2.2
  set S : Sylow 2 ↥H := hT'2.toSylow hT'odd with hSdef
  have hScoe : (S : Subgroup ↥H) = T.subgroupOf H := IsPGroup.toSylow_coe hT'2 hT'odd
  have hZT : Z ≤ T := fun z hz => (mem_omegaOneCenterOf_iff.mp (show z ∈ omegaOneCenterOf 2 T
    from hz)).1
  have hZH : Z ≤ H := hZT.trans hTH
  have hZS : Z.subgroupOf H ≤ CFSG.Quasithin.BlueprintB2.centerTorsion 2 (S : Subgroup ↥H) := by
    intro z hz
    have hz' : (z : G) ∈ omegaOneCenterOf 2 T := mem_subgroupOf.mp hz
    obtain ⟨hzT, hzc, hz2⟩ := mem_omegaOneCenterOf_iff.mp hz'
    rw [CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff, hScoe]
    refine ⟨mem_subgroupOf.mpr hzT, fun k hk => Subtype.ext ?_, Subtype.ext ?_⟩
    · exact (hzc k (mem_subgroupOf.mp hk)).symm
    · change (z : G) ^ 2 = 1
      exact hz2
  obtain ⟨-, hred, hZle, hagg⟩ :=
    CFSG.QuasithinUnique.Setup.qt_characteristic_p_Sylow_center_reduced_closure 2 hHc S hZS
  have hUmap : (normalClosure ((Z.subgroupOf H : Subgroup ↥H) : Set ↥H)).map H.subtype = U :=
    map_normalClosure_subgroupOf hZH
  have hUH : U ≤ H := hUmap ▸ map_subtype_le _
  have hUsub : U.subgroupOf H = normalClosure ((Z.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [← hUmap, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hZU : Z ≤ U := by
    rw [← hUmap]
    intro z hz
    exact ⟨⟨z, hZH hz⟩, hZle (mem_subgroupOf.mpr hz), rfl⟩
  have hUV : U ≤ qtnqVc H := by
    rw [← hUmap]
    exact map_mono hagg
  have hQ : (CFSG.pCore 2 ↥H).map H.subtype = pCoreOf 2 H := by
    unfold pCoreOf
    try with_reducible rfl
  have hVZ : qtnqVc H ≤ omegaOneCenterOf 2 (pCoreOf 2 H) := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (CFSG.Quasithin.qt_prime_reduced_aggregate_characteristic_maximal ↥H 2
      ).2.2.2.2.2.2.2.2.2 hv
    obtain ⟨hvQ, hvc, hv2⟩ := CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.mp hv'
    refine mem_omegaOneCenterOf_iff.mpr ⟨hQ ▸ mem_map_of_mem _ hvQ, fun q hq => ?_, ?_⟩
    · rw [← hQ] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      exact congrArg Subtype.val (hvc q' hq').symm
    · change (v : G) ^ 2 = 1
      exact congrArg Subtype.val hv2
  have hPU : pCoreOf 2 H ≤ centralizer (U : Set G) := fun p hp =>
    mem_centralizer_iff.mpr fun u hu => (mem_omegaOneCenterOf_iff.mp (hVZ (hUV hu))).2.1 p hp
  refine ⟨hUH, hUsub ▸ hred, hZU, hUV, hVZ, hPU, fun B hB hBM => ?_, ?_⟩
  · have hZB : ⁅Z, B⁆ ≠ ⊥ := by
      intro h0
      apply hBM
      rw [commutator_eq_bot_iff_le_centralizer] at h0
      exact (le_centralizer_iff.mp h0).trans h.centralizer_le
    have hUB : ⁅U, B⁆ ≠ ⊥ := fun h0 => hZB (le_bot_iff.mp (h0 ▸ commutator_mono hZU le_rfl))
    have hBloc := QuasithinUnique.Vol2Native.isLocal_of_mem_cComp hO2 hTs hB
    have hPB : ⁅omegaOneCenterOf 2 (pCoreOf 2 H), B⁆ ≠ ⊥ := fun h0 =>
      hZB (le_bot_iff.mp (h0 ▸ commutator_mono (hZU.trans (hUV.trans hVZ)) le_rfl))
    have hBH : B ≤ H := le_of_mem_cComp hB
    have hXmap : (B.subgroupOf H).map H.subtype = B := map_subgroupOf_eq_of_le hBH
    have hXp : Group.IsPerfect (B.subgroupOf H) := by
      refine Subgroup.isPerfect_iff.mpr ?_
      apply map_injective H.subtype_injective
      rw [map_commutator, hXmap, perfect_of_mem_cComp hB]
    have hPn : ((pCoreOf 2 H).subgroupOf H).Normal :=
      (normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    have hPmap : ((pCoreOf 2 H).subgroupOf H).map H.subtype = pCoreOf 2 H :=
      map_subgroupOf_eq_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    have hQmap : ((CFSG.pCore 2 ↥(B.subgroupOf H)).map (B.subgroupOf H).subtype).map
        H.subtype = pCoreOf 2 B := by
      have h1 := map_inSubgroup_pCore (B.subgroupOf H) 2
      rwa [hXmap] at h1
    have hQP : (CFSG.pCore 2 ↥(B.subgroupOf H)).map (B.subgroupOf H).subtype ≤
        (pCoreOf 2 H).subgroupOf H := by
      intro y hy
      rw [mem_subgroupOf]
      have h1 : (y : G) ∈ pCoreOf 2 B := by
        rw [← hQmap]
        exact mem_map_of_mem _ hy
      exact CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hB) h1
    have hiff := prime_residual_subnormal_core_center_action
      (R := (pCoreOf 2 H).subgroupOf H)
      (CFSG.Quasithin.B69.isSubnormal_subgroupOf_of_chain (subnormal_of_mem_cComp hB))
      (CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_isPerfect hXp)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_subtype :
        IsPGroup 2 ((pCoreOf 2 H).subgroupOf H)) hQP
    rw [commutator_eq_bot_iff_map_subtype, commutator_eq_bot_iff_map_subtype,
      map_omegaOneCenterOf, map_omegaOneCenterOf, hQmap, hPmap, hXmap] at hiff
    have hBf : quasithinIsFaithfulLocal T B :=
      (NQCore.qt_full_Sylow_local_characteristic_two h.qtke h.sylow hBloc).2.2.mpr
        fun h0 => hPB (hiff.mp h0)
    obtain ⟨B', hB', hBB'⟩ := faithful_maximal_local_exists LocDbl.local_double_embedding_exclusion
      h.simple h.nonabelian h.qtke h.sylow hBf
    exact ⟨hZB, hUB, hBf, B', hB', hBB', fun hB'M => hBM (hBB'.trans hB'M)⟩
  · constructor
    · intro hY
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      exact hY (sSup_le fun C hC => hall C hC.1 hC.2)
    · rintro ⟨B, hB, hBA, hBM⟩ hY
      exact hBM ((le_sSup ⟨hB, hBA⟩ : B ≤ nqComplementaryLayer H A).trans hY)

end CFSG.Quasithin.H13.NQBlock
