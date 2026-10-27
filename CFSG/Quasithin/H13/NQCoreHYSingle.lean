module

public import CFSG.Quasithin.H13.NQCoreHYTools
public import CFSG.Quasithin.H13.NQCoreUniversalConfine
public import CFSG.Quasithin.H13.AssemblyVocab
public import CFSG.LocalAnalysis.SteinbergCECComponentLocalFamily
public import CFSG.LocalAnalysis.SteinbergCCTwoSignalizerFaithfulness
public import CFSG.Quasithin.H13.NQCoreEscapingResidual

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

@[expose] def StmtFiveModelLocalChainRigid : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T D B : Subgroup G), quasithinIsSylowTwo T →
    ⁅D, D⁆ = D → T ≤ normalizer (D : Set G) → B ≤ D → B ≠ ⊥ → ⁅B, B⁆ = B →
    T ≤ normalizer (B : Set G) → QT13Five (↥D ⧸ CFSG.pCore 2 ↥D) → B = D

theorem map_closure_centralInvolutions {E F : Type*} [Group E] [Group F] (f : E →* F)
    (hf : Function.Injective f) (O : Subgroup E) :
    (closure {a : E | a ∈ O ∧ (∀ b ∈ O, a * b = b * a) ∧ a ^ 2 = 1}).map f =
      closure {z : F | z ∈ O.map f ⊓ centralizer (O.map f : Set F) ∧ z ^ 2 = 1} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ⟨haO, hac, ha2⟩, rfl⟩
    refine ⟨mem_inf.mpr ⟨⟨a, haO, rfl⟩, mem_centralizer_iff.mpr ?_⟩, by
      rw [← map_pow, ha2, map_one]⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hac b hb]
  · rintro ⟨hzOC, hz2⟩
    obtain ⟨⟨a, haO, rfl⟩, hzC⟩ := mem_inf.mp hzOC
    refine ⟨a, ⟨haO, fun b hb => hf ?_, hf (by rw [map_pow, hz2, map_one])⟩, rfl⟩
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.mp hzC (f b) ⟨b, hb, rfl⟩).symm

theorem map_map_pCore_eq_pCoreOf {G : Type*} [Group G] {H : Subgroup G} (Y : Subgroup ↥H) :
    ((CFSG.pCore 2 ↥Y).map Y.subtype).map H.subtype = pCoreOf 2 (Y.map H.subtype) := by
  set e : ↥Y ≃* ↥(Y.map H.subtype) := Y.equivMapOfInjective H.subtype H.subtype_injective
  have h1 : (CFSG.pCore 2 ↥Y).map e.toMonoidHom = CFSG.pCore 2 ↥(Y.map H.subtype) :=
    CFSG.pCore_map_iso 2 e
  have h2 : H.subtype.comp Y.subtype = (Y.map H.subtype).subtype.comp e.toMonoidHom := by
    ext y
    rfl
  rw [map_map, h2, ← map_map, h1, pCoreOf]

theorem quasithinV2_ne_bot_of_commutator {G : Type} [Group G] [Finite G] {H T : Subgroup G}
    (hchar : CharTwo H) (hTH : T ≤ H) (hRT : pCoreOf 2 H ≤ T) {Y : Subgroup ↥H} [hYn : Y.Normal]
    (hYp : ⁅Y, Y⁆ = Y) (hZY : ⁅quasithinOmegaOneCenter T, Y.map H.subtype⁆ ≠ ⊥) :
    quasithinV2 (Y.map H.subtype) ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup ↥H := CFSG.pCore 2 ↥H with hRdef
  have hRn : R.Normal := CFSG.pCore_normal
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup
  have hRmap : R.map H.subtype = pCoreOf 2 H := by rw [hRdef]; rfl
  have hYR : Y ≤ normalizer (R : Set ↥H) := by
    rw [normalizer_eq_top_iff.mpr hRn]
    exact le_top
  have hOR : CFSG.inSubgroup (CFSG.pCore 2) Y ≤ R := by
    have h1 := pCore_map_eq_inf_of_normal (Q := ↥H) (Y := Y)
    show (CFSG.pCore 2 ↥Y).map Y.subtype ≤ R
    rw [h1, hRdef]
    exact inf_le_right
  obtain ⟨-, -, hiff⟩ := CFSG.LocalAnalysis.perfect_two_signalizer_faithfulness hYp
    hYn.isSubnormal hR2 hYR hOR
  set Z : Subgroup ↥H := (quasithinOmegaOneCenter T).subgroupOf H with hZdef
  have hZT : quasithinOmegaOneCenter T ≤ T := fun z hz =>
    (CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.mp
      (NQTerm.quasithinOmegaOneCenter_le_centerTorsion T hz)).1
  have hZW : Z ≤ closure {s : ↥H | s ∈ R ∧ (∀ b ∈ R, s * b = b * s) ∧ s ^ 2 = 1} := by
    intro z hz
    obtain ⟨hzT, hzc, hz2⟩ := CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.mp
      (NQTerm.quasithinOmegaOneCenter_le_centerTorsion T hz)
    have hbR : ∀ b ∈ R, (b : G) ∈ T := fun b hb => hRT (hRmap ▸ mem_map_of_mem _ hb)
    have hzR : z ∈ R := by
      have h1 : (z : G) ∈ pCoreOf 2 H := hchar (mem_inf.mpr ⟨z.2, mem_centralizer_iff.mpr
        fun r hr => hzc r (hRT hr)⟩)
      rw [← hRmap] at h1
      obtain ⟨r, hr, hrz⟩ := h1
      rwa [show r = z from Subtype.ext hrz] at hr
    refine subset_closure ⟨hzR, fun b hb => Subtype.ext ?_, Subtype.ext hz2⟩
    exact (hzc b (hbR b hb)).symm
  have hZmap : Z.map H.subtype = quasithinOmegaOneCenter T :=
    Subgroup.map_subgroupOf_eq_of_le (hZT.trans hTH)
  have hW : ⁅closure {s : ↥H | s ∈ R ∧ (∀ b ∈ R, s * b = b * s) ∧ s ^ 2 = 1}, Y⁆ ≠ ⊥ := by
    intro hb
    apply hZY
    rw [← hZmap, ← map_commutator, eq_bot_iff]
    exact (map_mono (Subgroup.commutator_mono hZW le_rfl)).trans (by rw [hb, Subgroup.map_bot])
  have hV := hiff.mp hW
  intro hb
  apply hV
  apply map_injective H.subtype_injective
  rw [Subgroup.map_bot, map_commutator,
    map_closure_centralInvolutions H.subtype H.subtype_injective,
    show (CFSG.inSubgroup (CFSG.pCore 2) Y).map H.subtype = pCoreOf 2 (Y.map H.subtype) from
      map_map_pCore_eq_pCoreOf Y]
  exact hb

variable {G : Type} [Group G] [Finite G]

theorem minimal_escaping_single_factor
    (hD : LocalDoubleEmbeddingExclusion) (h37 : Vol2Native.A37ForSQTKCat)
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent)
    (hO : StmtSCComponentOrbits) (hN : StmtSCNormalExclusion) (hP : StmtSCPairedExclusion)
    (hI : StmtIntrinsicActionExclusion) (h1323 : Stmt13_1_2_three)
    (hrig : StmtFiveModelLocalChainRigid) {T L M : Subgroup G} (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M)
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M)
    {H₀ H : Subgroup G} (hH₀ : quasithinIsMaxTwoLocal H₀) (hTH₀ : T ≤ H₀)
    (hTH : T ≤ H) (hHH₀ : H ≤ H₀) (hHM : ¬ H ≤ M)
    (hmin : ∀ K : Subgroup G, T ≤ K → K ≤ H₀ → ¬ K ≤ M → Nat.card H ≤ Nat.card K)
    [IsSimpleGroup ↥((CFSG.perfectResidual ↥H).map
      (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)))] :
    quasithinIsCComponent ((CFSG.perfectResidual ↥H).map H.subtype) H ∧
      (quasithinIsMaximalLocal T ((CFSG.perfectResidual ↥H).map H.subtype) ∧
        quasithinIsFaithfulLocal T ((CFSG.perfectResidual ↥H).map H.subtype)) ∧
      ⁅quasithinOmegaOneCenter T, (CFSG.perfectResidual ↥H).map H.subtype⁆ ≠ ⊥ ∧
      (∀ D : Subgroup G, quasithinIsLocal T D → (CFSG.perfectResidual ↥H).map H.subtype ≤ D →
        D = (CFSG.perfectResidual ↥H).map H.subtype) ∧
      QT13Five (↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
        CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  obtain ⟨-, hR1, -, -, -, -, -⟩ := minimal_escaping_basic h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨⟨hYa1, hYap, -⟩, ⟨-, hYaM, -⟩, -, -⟩ :=
    minimal_escaping_structure h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨hT'syl, hTn', hT'X', hX'lt, hmax', hns'⟩ :=
    minimal_escaping_abstract h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨-, ⟨-, -, hJsolv⟩, -⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hT'syl hTn' hT'X' hX'lt hmax'
  obtain ⟨-, -, -, hY'p, hY'c⟩ :=
    perfectResidual_minimal_structure hT'syl hTn' hT'X' hX'lt hmax' hns'
  have := hY'c
  have hY'n : (CFSG.perfectResidual ↥H).Normal := inferInstance
  set Ya := (CFSG.perfectResidual ↥H).map H.subtype with hYa
  have hna : ¬ IsMulCommutative ↥((CFSG.perfectResidual ↥H).map
      (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))) := by
    intro hc
    have hS1 : Nontrivial ↥((CFSG.perfectResidual ↥H).map
        (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))) := IsSimpleGroup.toNontrivial
    apply (nontrivial_iff_ne_bot _).mp hS1
    have hperf : ⁅(CFSG.perfectResidual ↥H).map
        (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)),
        (CFSG.perfectResidual ↥H).map (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))⁆ =
        (CFSG.perfectResidual ↥H).map (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)) := by
      rw [← map_commutator, Subgroup.isPerfect_iff.mp hY'p]
    rw [← hperf]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => ?_
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hc.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hYC := isCComponent_perfectResidual_of_isSimpleGroup hJsolv hna
  have hYaC : Ya ∈ cComp H := map_subtype_mem_cComp (mem_cComp_top_iff_isCComponent.mpr hYC)
  have hTi : ¬ 2 ∣ (T.subgroupOf H).index := fun hd =>
    h.sylow.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le hTH))
  have hLoc : quasithinIsLocal T Ya := by
    have h1 := (CFSG.LocalAnalysis.Ccomponent_in_local_family hR1 h.sylow.1 hTH hTi
      (H13.quasithinIsCComponent_open_iff.mp hYaC)).2
    exact H13.quasithinIsLocal_open_iff.mpr h1
  have hZY : ⁅quasithinOmegaOneCenter T, Ya⁆ ≠ ⊥ := by
    intro hb
    apply hYaM
    refine le_trans (fun y hy => ?_) h.centralizer_le
    rw [mem_centralizer_iff]
    intro z hz
    have h1 : ⁅z, y⁆ ∈ ⁅quasithinOmegaOneCenter T, Ya⁆ := commutator_mem_commutator hz hy
    rwa [hb, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have hT'G : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.sylow.2
  have hchar : CharTwo H :=
    charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot h.qtke.2.1 hT'G hTH hR1
  have hRT : pCoreOf 2 H ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowIn_of_quasithin h.sylow hTH)
  have hV2 : quasithinV2 Ya ≠ ⊥ :=
    quasithinV2_ne_bot_of_commutator hchar hTH hRT (Subgroup.isPerfect_iff.mp hY'p) hZY
  have hYf : quasithinIsFaithfulLocal T Ya :=
    (qt_full_Sylow_local_characteristic_two h.qtke h.sylow hLoc).2.2.mpr hV2
  obtain ⟨D, ⟨hDmax, hDf⟩, hYD⟩ :=
    H13.faithful_maximal_local_exists hD h.simple h.nonabelian h.qtke h.sylow hYf
  have hYaH : Ya ≤ H := map_subtype_le _
  have hHnY : H ≤ normalizer (Ya : Set G) := by
    refine (normal_subgroupOf_iff_le_normalizer hYaH).mp ?_
    have hYsub : ((CFSG.perfectResidual ↥H).map H.subtype).subgroupOf H =
        CFSG.perfectResidual ↥H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [hYa, hYsub]
    exact hY'n
  have hTYn : T ≤ normalizer (Ya : Set G) := hTH.trans hHnY
  have hchain := H13.local_normalizer_chain_equality_of h37 hD h.simple h.nonabelian h.qtke hLoc
    hDmax.1 hYD
  have hTD : T ≤ normalizer (D : Set G) := by
    intro t ht
    have h1 : t ∈ T ⊓ normalizer (Ya : Set G) := mem_inf.mpr ⟨ht, hTYn ht⟩
    rw [hchain] at h1
    exact (mem_inf.mp h1).2
  have hDq : CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D) := by
    by_contra hDq
    obtain ⟨hDM, -, -⟩ := every_sylow_normalized_maximal_nonquasisimple_local_is_confined
      hA7u hA7n hO hN hP hI h hDmax hDf hTD hDq
    exact hYaM (hYD.trans hDM)
  have h5 := h1323 G T D h.simple h.nonabelian h.qtke h.sylow h.not_excluded hDmax hDf hDq
  have hYeq : Ya = D := hrig G T D Ya h.sylow hDmax.1.2.1.2.1 hTD hYD hYa1 hYap hTYn h5
  subst hYeq
  exact ⟨hYaC, ⟨hDmax, hDf⟩, hZY, fun D' hD' hYD' => hDmax.2 D' hD' hYD', h5⟩

end CFSG.Quasithin.H13.NQCore
