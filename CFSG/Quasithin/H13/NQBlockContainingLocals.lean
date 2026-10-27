module

public import CFSG.Quasithin.H13.NQBlockContainingCore
public import CFSG.Quasithin.H13.AssemblyLocal
public import CFSG.Quasithin.H13.NQCoreLocalChar
public import CFSG.LocalAnalysis.SteinbergCEFaithfulPerfectInclusion
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SteinbergCCTwoSignalizerFaithfulness
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.NQBlockFiveModelRigidity

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

variable {G : Type} [Group G]

theorem closure_omegaOne_eq (Q : Subgroup G) :
    closure {a | a ∈ Q ∧ (∀ b ∈ Q, a * b = b * a) ∧ a ^ 2 = 1} = omegaOneCenterOf 2 Q := by
  unfold omegaOneCenterOf
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq, mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨haQ, hac, ha2⟩
    exact ⟨⟨haQ, fun b hb => (hac b hb).symm⟩, ha2⟩
  · rintro ⟨⟨haQ, hac⟩, ha2⟩
    exact ⟨haQ, fun b hb => (hac b hb).symm, ha2⟩

variable [Finite G]

theorem isSylowTwoOf_top_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) :
    QuasithinUnique.IsSylowTwoOf T ⊤ := by
  refine ⟨le_top, h.sylow.1, ?_⟩
  change ¬ 2 ∣ T.relIndex ⊤
  rw [relIndex_top_right]
  exact h.sylow.2

theorem isSylowTwoOf_of_qtnq {T L M H : Subgroup G} (h : QTNQ T L M) (hTH : T ≤ H) :
    QuasithinUnique.IsSylowTwoOf T H :=
  ⟨hTH, h.sylow.1, fun h2 => h.sylow.2 (h2.trans (relIndex_dvd_index_of_le hTH))⟩

theorem vK_eq {T L M : Subgroup G} (h : QTNQ T L M)
    {R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L) :
    ⁅omegaOneCenterOf 2 (pCoreOf 2 (nqOriginalK T L)) ⊓ centralizer (R : Set G),
        nqOriginalK T L⁆ = ⁅omegaOneCenterOf 2 R, nqOriginalK T L⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := nqOriginalK T L with hKdef
  obtain ⟨-, hTK, hKp, -⟩ := original_K_quotient_facts h
  obtain ⟨-, -, -, -, -, -, hKTR, -⟩ := original_radical_normalizer_local_and_Thompson_failure h hR
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hR2 : IsPGroup 2 R := h.sylow.1.to_le hRT
  have hKR : K ≤ normalizer (R : Set G) := le_sup_left.trans hKTR
  obtain ⟨-, -, -, -, -, -, -, -, -, hRKT⟩ :=
    original_common_residual_is_faithful_and_has_exact_reduced_action_kernel h hR
  have hKTQ : K ⊔ T ≤ normalizer (pCoreOf 2 K : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hQKR : pCoreOf 2 K ≤ R := by
    rw [hRKT]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left) hKTQ
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  apply le_antisymm
  · refine commutator_mono (fun x hx => ?_) le_rfl
    obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
    obtain ⟨hxQ, -, hx2'⟩ := mem_omegaOneCenterOf_iff.mp hx1
    exact mem_omegaOneCenterOf_iff.mpr ⟨hQKR hxQ,
      fun r hr => ((mem_centralizer_iff.mp hx2) r hr).symm, hx2'⟩
  ·
    set B := K ⊔ T with hBdef
    have hinj := B.subtype_injective
    have hKB : K ≤ B := le_sup_left
    have hRB : R ≤ B := hRT.trans le_sup_right
    have hmX : (K.subgroupOf B).map B.subtype = K := map_subgroupOf_eq_of_le hKB
    have hmS : (R.subgroupOf B).map B.subtype = R := map_subgroupOf_eq_of_le hRB
    have hmO : (inSubgroup (CFSG.pCore 2) (K.subgroupOf B)).map B.subtype = pCoreOf 2 K := by
      rw [map_inSubgroup_pCore, hmX]
    have hX'p : ⁅K.subgroupOf B, K.subgroupOf B⁆ = K.subgroupOf B := by
      apply map_injective hinj
      rw [map_commutator, hmX, hKp]
    have hKn : (K.subgroupOf B).Normal :=
      (normal_subgroupOf_iff_le_normalizer hKB).mpr (sup_le le_normalizer hTK)
    have hS'2 : IsPGroup 2 ↥(R.subgroupOf B) := hR2.comap_subtype
    have hX'S' : K.subgroupOf B ≤ normalizer ((R.subgroupOf B : Subgroup B) : Set B) := by
      intro x hx
      rw [mem_normalizer_iff]
      intro n
      simp only [mem_subgroupOf, coe_mul, coe_inv]
      exact mem_normalizer_iff.mp (hKR hx) n
    have hO'S' : inSubgroup (CFSG.pCore 2) (K.subgroupOf B) ≤ R.subgroupOf B := by
      intro o ho
      rw [mem_subgroupOf]
      exact hQKR (hmO ▸ mem_map_of_mem B.subtype ho)
    obtain ⟨hW, -, -⟩ := CFSG.LocalAnalysis.perfect_two_signalizer_faithfulness hX'p
      hKn.isSubnormal hS'2 hX'S' hO'S'
    have h1 := congrArg (Subgroup.map B.subtype) hW
    rw [map_commutator, map_commutator,
      CFSG.LocalAnalysis.FaithfulPerfectInclusion.map_closure_omegaOne _ hinj, hmS, hmX,
      closure_omegaOne_eq] at h1
    rw [h1]
    refine commutator_mono ?_ le_rfl
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hvV, hvC⟩ := mem_inf.mp hv
    refine mem_inf.mpr ⟨?_, mem_centralizer_iff.mpr fun r hr => ?_⟩
    · have hv' := mem_map_of_mem B.subtype hvV
      rw [map_commutator, CFSG.LocalAnalysis.FaithfulPerfectInclusion.map_closure_omegaOne _ hinj,
        hmO, hmX, closure_omegaOne_eq] at hv'
      exact commutator_omegaOneCenterOf_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) hv'
    · exact congrArg Subtype.val ((mem_centralizer_iff.mp hvC) ⟨r, hRB hr⟩
        (mem_subgroupOf.mpr hr))

theorem containing_normal_facts {T L M : Subgroup G}
    (h : QTNQ T L M) {R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L)
    {E Y : Subgroup G} (hTE : T ≤ E) (hE : pCoreOf 2 E ≠ ⊥) (hYE : Y ≤ E)
    (hEY : E ≤ normalizer (Y : Set G)) (hYp : ⁅Y, Y⁆ = Y) (hKY : nqOriginalK T L ≤ Y) :
    QuasithinUnique.CharTwo E ∧ pCoreOf 2 E ≤ R ∧ pCoreOf 2 Y = Y ⊓ pCoreOf 2 E ∧
      ⁅omegaOneCenterOf 2 R, nqOriginalK T L⁆ ≤ ⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆ ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆ ≤ ⁅omegaOneCenterOf 2 (pCoreOf 2 Y), Y⁆ ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 Y), Y⁆ ≤ omegaOneCenterOf 2 (pCoreOf 2 Y) ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆ ≤ E ∧
      ((⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆ : Subgroup G).subgroupOf E).Normal ∧
      CFSG.IsElementaryAbelian 2 ↥⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆ ∧
      ⁅⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆, Y⁆ = ⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆ ∧
      ((nqOriginalK T L ⊓ centralizer
          ((⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆ : Subgroup G) : Set G)).subgroupOf
        (nqOriginalK T L)).Normal ∧
      nqOriginalK T L ⊓ centralizer
          ((⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆ : Subgroup G) : Set G) ≤
        pCoreOf 2 (nqOriginalK T L) ∧
      ⁅omegaOneCenterOf 2 R, nqOriginalK T L⁆ ≠ ⊥ ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 Y), Y⁆ ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := nqOriginalK T L with hKdef
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hE2 : QuasithinUnique.CharTwo E := QuasithinUnique.charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot
    h.qtke.2.1 (isSylowTwoOf_top_of_qtnq h) hTE hE
  have hYn : (Y.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hYE).mpr hEY
  obtain ⟨-, -, -, hcore⟩ :=
    normal_original_K_overgroup_factors_have_core_containment_and_commutator_transport h hR
  have hQR : pCoreOf 2 E ≤ R := (hcore E Y (sup_le (hKY.trans hYE) hTE) hYE hYn).2.1
  obtain ⟨-, hQY, hDW, hWZ, hWE, hEW, hWel, hWW, hWV⟩ :=
    nested_core_centers hE2 (hRT.trans hTE) hQR hYE hEY hYp hKY
  set W := ⁅omegaOneCenterOf 2 (pCoreOf 2 E), Y⁆ with hWdef
  obtain ⟨-, -, -, -, hVK, -⟩ :=
    original_common_residual_is_faithful_and_has_exact_reduced_action_kernel h hR
  obtain ⟨hVK1, -, -, -, -, hKC, -⟩ := hVK _ rfl
  rw [vK_eq h hR] at hVK1 hKC
  have hKW : K ≤ normalizer (W : Set G) := (hKY.trans hYE).trans hEW
  have hCn : ((K ⊓ centralizer (W : Set G)).subgroupOf K).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro k hk
    have hkC : k ∈ normalizer (centralizer (W : Set G) : Set G) :=
      mem_normalizer_of_conj_mem (fun c hc => conj_mem_centralizer_of_normalizer (hKW hk) hc)
        fun c hc => by
          have := conj_mem_centralizer_of_normalizer (hKW (K.inv_mem hk)) hc
          rwa [inv_inv] at this
    exact mem_normalizer_inf (le_normalizer hk) hkC
  have hCQ : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K := by
    rw [← hKC]
    exact inf_le_inf_left K (centralizer_le hDW)
  have hV1 : ⁅omegaOneCenterOf 2 (pCoreOf 2 Y), Y⁆ ≠ ⊥ := fun h0 =>
    hVK1 (le_bot_iff.mp (h0 ▸ hDW.trans hWV))
  have hWY : ⁅omegaOneCenterOf 2 (pCoreOf 2 Y), Y⁆ ≤ omegaOneCenterOf 2 (pCoreOf 2 Y) :=
    commutator_omegaOneCenterOf_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  exact ⟨hE2, hQR, by rw [← hQY, inf_comm], hDW, hWV, hWY, hWE,
    (normal_subgroupOf_iff_le_normalizer hWE).mpr hEW, hWel, hWW, hCn, hCQ, hVK1, hV1⟩

theorem nqOriginalK_ne {T L M : Subgroup G} (h : QTNQ T L M) :
    nqOriginalK T L ≠ L := by
  intro hKL
  obtain ⟨-, -, -, hsimple, hnc, -⟩ := original_K_quotient_facts h
  have := hsimple
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  apply h.not_quasisimple
  rw [hKL] at hq
  exact hq

theorem exists_maximalLocal_ge {T D : Subgroup G} (hD : quasithinIsLocal T D) :
    ∃ D' : Subgroup G, quasithinIsMaximalLocal T D' ∧ D ≤ D' := by
  obtain ⟨D', hD'⟩ := Set.Finite.exists_maximal
    (s := {Y : Subgroup G | quasithinIsLocal T Y ∧ D ≤ Y}) (Set.toFinite _) ⟨D, hD, le_rfl⟩
  exact ⟨D', ⟨hD'.1.1, fun Y hY hDY =>
    le_antisymm (hD'.2 ⟨hY, hD'.1.2.trans hDY⟩ hDY) hDY⟩, hD'.1.2⟩

theorem containing_local_facts
    {T L M : Subgroup G} (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) {D : Subgroup G} (hD : quasithinIsLocal T D)
    (hKD : nqOriginalK T L ≤ D) :
    T ≤ normalizer (D : Set G) ∧ QuasithinUnique.CharTwo (D ⊔ T) ∧ pCoreOf 2 (D ⊔ T) ≠ ⊥ ∧
      pCoreOf 2 (D ⊔ T) ≤ R ∧ pCoreOf 2 D = D ⊓ pCoreOf 2 (D ⊔ T) ∧
      ⁅omegaOneCenterOf 2 R, nqOriginalK T L⁆ ≤ ⁅omegaOneCenterOf 2 (pCoreOf 2 (D ⊔ T)), D⁆ ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 (D ⊔ T)), D⁆ ≤ ⁅omegaOneCenterOf 2 (pCoreOf 2 D), D⁆ ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 D), D⁆ ≤ omegaOneCenterOf 2 (pCoreOf 2 D) ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 (D ⊔ T)), D⁆ ≤ D ⊔ T ∧
      ((⁅omegaOneCenterOf 2 (pCoreOf 2 (D ⊔ T)), D⁆ : Subgroup G).subgroupOf (D ⊔ T)).Normal ∧
      CFSG.IsElementaryAbelian 2 ↥⁅omegaOneCenterOf 2 (pCoreOf 2 (D ⊔ T)), D⁆ ∧
      ⁅⁅omegaOneCenterOf 2 (pCoreOf 2 (D ⊔ T)), D⁆, D⁆ =
        ⁅omegaOneCenterOf 2 (pCoreOf 2 (D ⊔ T)), D⁆ ∧
      ((nqOriginalK T L ⊓ centralizer
          ((⁅omegaOneCenterOf 2 (pCoreOf 2 (D ⊔ T)), D⁆ : Subgroup G) : Set G)).subgroupOf
        (nqOriginalK T L)).Normal ∧
      nqOriginalK T L ⊓ centralizer
          ((⁅omegaOneCenterOf 2 (pCoreOf 2 (D ⊔ T)), D⁆ : Subgroup G) : Set G) ≤
        pCoreOf 2 (nqOriginalK T L) ∧
      quasithinIsFaithfulLocal T D := by
  classical
  set K := nqOriginalK T L with hKdef
  obtain ⟨hKf, -⟩ := original_common_residual_is_faithful_and_has_exact_reduced_action_kernel h hR
  obtain ⟨-, hTK, -⟩ := original_K_quotient_facts h
  have hTD : T ≤ normalizer (D : Set G) := fun t ht =>
    (local_normalizer_chain_inclusion h.simple h.nonabelian h.qtke hKf.1 hD hKD
      (mem_inf.mpr ⟨ht, hTK ht⟩)).2
  obtain ⟨hE2, hQR, hQY, hDW, hWV, hWY, hWE, hWn, hWel, hWW, hCn, hCQ, -, hV1⟩ :=
    containing_normal_facts h hR le_sup_right hD.2.2.2 le_sup_left (sup_le le_normalizer hTD)
      hD.2.1.2.1 hKD
  refine ⟨hTD, hE2, hD.2.2.2, hQR, hQY, hDW, hWV, hWY, hWE, hWn, hWel, hWW, hCn, hCQ, ?_⟩
  exact (NQCore.qt_full_Sylow_local_characteristic_two h.qtke h.sylow hD).2.2.mpr hV1

theorem not_qt13Five_of_maximalLocal {T L M : Subgroup G}
    (h : QTNQ T L M) {D : Subgroup G} (hD : quasithinIsMaximalLocal T D)
    (hKD : nqOriginalK T L ≤ D) (hTD : T ≤ normalizer (D : Set G)) :
    ¬ QT13Five (↥D ⧸ CFSG.pCore 2 ↥D) := by
  intro h5
  have hDn : (D.subgroupOf (D ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hTD)
  obtain ⟨hDK, -, -⟩ := (original_K_containing_perfect_normal_overgroups_have_five_model_rigidity
    h (sup_le_sup_right hKD T) le_sup_left hDn hD.1.2.1.2.1 hKD).2.2.2.2.1 h5
  obtain ⟨hKL, -⟩ := original_K_quotient_facts h
  apply nqOriginalK_ne h
  rw [← hDK]
  exact (hD.2 L h.maximal_local.1 (hDK ▸ hKL)).symm

end CFSG.Quasithin.H13.NQBlock
