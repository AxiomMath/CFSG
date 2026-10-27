module

public import CFSG.Quasithin.H13.NQCoreT2Gap
public import CFSG.Quasithin.H13.NQCoreEscapingCore
public import CFSG.Quasithin.H13.LocDblSporadic
public import CFSG.Quasithin.Vol2.Ch10SecABasic
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Background.B69E22Link
public import CFSG.Quasithin.H13.NQBlockContainingLocals
public import CFSG.Quasithin.H13.StatementsL1

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

theorem exists_mul_ne_mul_of_isPerfect {Q : Type*} [Group Q] [IsSimpleGroup Q]
    [Group.IsPerfect Q] : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  exact Group.IsPerfect.not_isMulCommutative Q ⟨⟨fun a b => hc a b⟩⟩

variable {G : Type} [Group G] [Finite G]

theorem faithfulLocal_of_mem_cComp_of_not_le {T L M H B : Subgroup G} (h : QTNQ T L M)
    (hTH : T ≤ H) (hO2 : pCoreOf 2 H ≠ ⊥) (hB : B ∈ cComp H) (hBM : ¬ B ≤ M) :
    quasithinIsFaithfulLocal T B := by
  classical
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs := isSylowTwoOf_of_qtnq h hTH
  have hH2 : QuasithinUnique.CharTwo H :=
    QuasithinUnique.charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot h.qtke.2.1
      (isSylowTwoOf_top_of_qtnq h) hTH hO2
  have hPT : pCoreOf 2 H ≤ T := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTs
  have hZP : quasithinOmegaOneCenter T ≤ omegaOneCenterOf 2 (pCoreOf 2 H) := by
    intro z hz
    obtain ⟨hzT, hzc, hz2⟩ := mem_omegaOneCenterOf_iff.mp (show z ∈ omegaOneCenterOf 2 T from hz)
    have hzC : z ∈ centralizer (pCoreOf 2 H : Set G) :=
      mem_centralizer_iff.mpr fun q hq => (hzc q (hPT hq)).symm
    exact mem_omegaOneCenterOf_iff.mpr ⟨hH2 ⟨hTH hzT, hzC⟩, fun q hq => hzc q (hPT hq), hz2⟩
  have hZB : ⁅quasithinOmegaOneCenter T, B⁆ ≠ ⊥ := by
    intro h0
    apply hBM
    rw [commutator_eq_bot_iff_le_centralizer] at h0
    exact (le_centralizer_iff.mp h0).trans h.centralizer_le
  have hPB : ⁅omegaOneCenterOf 2 (pCoreOf 2 H), B⁆ ≠ ⊥ := fun h0 =>
    hZB (le_bot_iff.mp (h0 ▸ commutator_mono hZP le_rfl))
  have hBloc := QuasithinUnique.Vol2Native.isLocal_of_mem_cComp hO2 hTs hB
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
  exact (NQCore.qt_full_Sylow_local_characteristic_two h.qtke h.sylow hBloc).2.2.mpr
    fun h0 => hPB (hiff.mp h0)

theorem stmtEscapingPairExcluded_of (h1001 : Stmt10_0_1)
    : NQCore.StmtEscapingPairExcluded := by
  intro G _ _ T L M h hTI hW H₀ H hH₀ hTH₀ hTH hHH₀ hHM hmin
  classical
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hO2, -, -, -, -, hmaxsub⟩ :=
    NQCore.minimal_escaping_basic h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨-, ⟨-, hYM, -⟩, -⟩ :=
    NQCore.minimal_escaping_structure h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨hT'syl, hTn', hT'X', hX'lt, hmax', -⟩ :=
    NQCore.minimal_escaping_abstract h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨-, ⟨-, -, hJsolv⟩, -⟩ :=
    CFSG.QuasithinUnique.Setup.qt_A7_unique_Sylow_overgroup_core_and_simple_section hT'syl hTn'
      hT'X' hX'lt hmax'
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTs := isSylowTwoOf_of_qtnq h hTH
  obtain ⟨B, hB, hBM⟩ : ∃ B ∈ cComp H, ¬ B ≤ M := by
    by_contra hall
    push Not at hall
    apply hYM
    rw [← perfectCore_eq_map_perfectResidual,
      ← QuasithinUnique.Vol2Native.lemma_1_2_1_one hloc
        QuasithinUnique.Vol2Native.a39ForSQTKCat_proved hO2]
    exact sSup_le hall
  have hBH : B ≤ H := le_of_mem_cComp hB
  have hBloc : quasithinIsLocal T B :=
    QuasithinUnique.Vol2Native.isLocal_of_mem_cComp hO2 hTs hB
  have hBf := faithfulLocal_of_mem_cComp_of_not_le h hTH hO2 hB hBM
  have hTB : T ≤ normalizer (B : Set G) := by
    obtain ⟨D, hDm, hBD⟩ := exists_maximalLocal_ge hBloc
    have hDf := local_faithfulness_upward LocDbl.local_double_embedding_exclusion h.simple
      h.nonabelian h.qtke h.sylow hDm.1 hBD hBf
    have hTD : T ≤ normalizer (D : Set G) := by
      have hDc : D ∈ cComp (D ⊔ T) := CFSG.Quasithin.cComp_of_isLocal hDm.1
      rcases QuasithinUnique.Vol2Native.lemma_1_2_1_three hloc
          QuasithinUnique.Vol2Native.a37ForSQTKCat_proved Vol2.Ch10.SecA.a38ForSQTKCat_proved
          hDm.1.2.2.2 hDc with hn | ⟨-, htypes⟩
      · exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)
      · have hs := QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
        have hDp : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hDc)
        have hnab := exists_mul_ne_mul_of_isPerfect (Q := ↥D ⧸ CFSG.pCore 2 ↥D)
        exact h1001 G T D h.simple h.nonabelian h.qtke h.sylow hDm hDf
          (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
    have heq := local_normalizer_chain_equality_of QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
      LocDbl.local_double_embedding_exclusion h.simple h.nonabelian h.qtke hBloc hDm.1 hBD
    intro t ht
    have h1 : t ∈ T ⊓ normalizer (D : Set G) := ⟨ht, hTD ht⟩
    rw [← heq] at h1
    exact h1.2
  have hBTH : B ⊔ T = H := by
    by_contra hne
    have hlt : B ⊔ T < H := lt_of_le_of_ne (sup_le hBH hTH) hne
    exact hBM (le_sup_left.trans ((hmaxsub _ le_sup_right hlt).trans inf_le_right))
  have hHB : H ≤ normalizer (B : Set G) := hBTH ▸ sup_le le_normalizer hTB
  have hBn : (B.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hBH).mpr hHB
  have hBp : Group.IsPerfect ↥(B.subgroupOf H) := by
    refine Subgroup.isPerfect_iff.mpr ?_
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hBH, perfect_of_mem_cComp hB]
  have hY : CFSG.perfectResidual ↥H = B.subgroupOf H := by
    obtain ⟨-, -, -, -, hiff, -⟩ := CFSG.perfect_residual_characterization (G := ↥H)
    refine le_antisymm ((hiff (B.subgroupOf H)).mp ?_)
      ((CFSG.perfect_residual_transport (MonoidHom.id ↥H)).2.2 _ hBp)
    have hp : IsPGroup 2 (↥H ⧸ B.subgroupOf H) := by
      intro x
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective x
      have hy' : y ∈ ((B ⊔ T : Subgroup G) : Set G) := hBTH ▸ hy
      rw [Subgroup.coe_mul_of_right_le_normalizer_left B T hTB, Set.mem_mul] at hy'
      obtain ⟨b, hb, t, ht, rfl⟩ := hy'
      obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, ht⟩
      have htk : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
      refine ⟨k, ?_⟩
      have e : (⟨b * t, hy⟩ : ↥H) = ⟨b, hBH hb⟩ * ⟨t, hTH ht⟩ := rfl
      have hb1 : ((⟨b, hBH hb⟩ : ↥H) : ↥H ⧸ B.subgroupOf H) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hb
      have ht1 : (⟨t, hTH ht⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext htk
      rw [e, QuotientGroup.mk_mul, hb1, one_mul, ← QuotientGroup.mk_pow, ht1, QuotientGroup.mk_one]
    have := hp.isNilpotent
    infer_instance
  have hψk : ((QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)).comp
      (Subgroup.inclusion hBH)).ker = CFSG.solvableRadical ↥B := by
    apply le_antisymm
    · have hle : ∀ x : ↥((QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)).comp
          (Subgroup.inclusion hBH)).ker,
          ((Subgroup.inclusion hBH).comp (MonoidHom.ker _).subtype) x ∈
            kerIn ((H ⊓ M).subgroupOf H) ⊤ := fun x => by
        have h1 := MonoidHom.mem_ker.mp x.2
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      have hf : Function.Injective
          (((Subgroup.inclusion hBH).comp (MonoidHom.ker _).subtype).codRestrict _ hle) := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : ↥(kerIn ((H ⊓ M).subgroupOf H) ⊤) => ((z : ↥H) : G)) hxy
      have hks := Group.isSolvable_of_isSolvable_injective hf
      exact le_sSup ⟨inferInstance, hks⟩
    · intro r hr
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      have hRH : (CFSG.solvableRadical ↥B).map B.subtype ≤ H := (map_subtype_le _).trans hBH
      have hHR : H ≤ normalizer (((CFSG.solvableRadical ↥B).map B.subtype : Subgroup G) : Set G) :=
        hHB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
      have hRs : Group.IsSolvable ↥((CFSG.solvableRadical ↥B).map B.subtype) := by
        have := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := ↥B)
        exact Group.isSolvable_of_surjective (f := ((CFSG.solvableRadical ↥B).equivMapOfInjective
          B.subtype B.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
      have hTsol : Group.IsSolvable ↥T := by
        have := h.sylow.1.isNilpotent
        infer_instance
      have hRT := CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer (hTH.trans hHR) hRs
        hTsol
      have hRM : (CFSG.solvableRadical ↥B).map B.subtype ≤ M :=
        le_sup_left.trans (NQCore.le_of_isSolvable_of_TI h hTI hW le_sup_right hRT)
      have hRn : (((CFSG.solvableRadical ↥B).map B.subtype).subgroupOf H).Normal :=
        (normal_subgroupOf_iff_le_normalizer hRH).mpr hHR
      have hRJ : ((CFSG.solvableRadical ↥B).map B.subtype).subgroupOf H ≤
          kerIn ((H ⊓ M).subgroupOf H) ⊤ :=
        CFSG.Quasithin.le_kerIn_of_le_normalizer
          (fun x hx => mem_subgroupOf.mpr (mem_inf.mpr ⟨x.2, hRM (mem_subgroupOf.mp hx)⟩))
          (Subgroup.normalizer_eq_top_iff.mpr hRn).ge
      exact hRJ (mem_subgroupOf.mpr (mem_map_of_mem B.subtype hr))
  have hBc : CFSG.IsCComponent (⊤ : Subgroup ↥B) := by
    have h2 : B ∈ cComp B := cComp_mem_of_le hB le_rfl hBH
    have h4 := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp h2)
    rwa [subgroupOf_self] at h4
  obtain ⟨hBs, -⟩ := simple_radical_quotient_of_isCComponent_top hBc
  have := hBs
  have hψr : ((QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)).comp
      (Subgroup.inclusion hBH)).range =
        (B.subgroupOf H).map (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [hY, ← hψr]
  exact ((QuotientGroup.quotientKerEquivRange _).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hψk)).isSimpleGroup

end CFSG.Quasithin.H13.NQBlock
