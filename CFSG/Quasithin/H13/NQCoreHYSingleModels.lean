module

public import CFSG.Quasithin.H13.NQCoreHYSingle
public import CFSG.Quasithin.H13.NQCoreAlt6Exclusion

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

theorem layer_eq_top_center_eq_bot_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : CFSG.layer S = ⊤ ∧ center S = ⊥ :=
  ⟨CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Unit) (S := fun _ => S) (fun _ => hna)
    (MulEquiv.piUnique fun _ : Unit => S).symm, center_eq_bot_of_isSimpleGroup hna⟩

theorem exists_mul_ne_of_not_isMulCommutative {Q : Type*} [Group Q] {S : Subgroup Q}
    (h : ¬ IsMulCommutative ↥S) : ∃ a b : ↥S, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  exact h ⟨⟨hab⟩⟩

theorem exists_mul_ne_of_quotient_center {Q S : Type*} [Group Q] [Group S] [Nontrivial S]
    (e : Q ⧸ center Q ≃* S) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  apply hs
  obtain ⟨x, rfl⟩ := e.surjective s
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ∈ center Q := mem_center_iff.mpr fun h => hab h g
  rw [(QuotientGroup.eq_one_iff g).mpr hg, map_one]

variable {G : Type} [Group G] [Finite G]

theorem minimal_escaping_single_factor_center
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
    Nat.card (((CFSG.perfectResidual ↥H ⊓ kerIn ((H ⊓ M).subgroupOf H) ⊤).subgroupOf
        (CFSG.perfectResidual ↥H)).map
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H)))) = 1 ∨
      (Nat.card (((CFSG.perfectResidual ↥H ⊓ kerIn ((H ⊓ M).subgroupOf H) ⊤).subgroupOf
        (CFSG.perfectResidual ↥H)).map
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H)))) = 3 ∧
        Nonempty (↥((CFSG.perfectResidual ↥H).map
          (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))) ≃* alternatingGroup (Fin 6))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, h5a⟩ := minimal_escaping_single_factor hD h37 hA7u hA7n hO hN hP hI h1323
    hrig h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  have hbasic := minimal_escaping_basic h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨hT'syl, hTn', hT'X', hX'lt, hmax', hns'⟩ :=
    minimal_escaping_abstract h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨⟨hRJ, -⟩, ⟨hJnil, hJodd, -⟩, -⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hT'syl hTn' hT'X' hX'lt hmax'
  obtain ⟨-, -, -, hYp, hYc⟩ :=
    perfectResidual_minimal_structure hT'syl hTn' hT'X' hX'lt hmax' hns'
  have := hYc
  have hYn : (CFSG.perfectResidual ↥H).Normal := inferInstance
  have hnaS : ∃ a b : ↥((CFSG.perfectResidual ↥H).map
      (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))), a * b ≠ b * a := by
    refine exists_mul_ne_of_not_isMulCommutative fun hc => ?_
    have hS1 : Nontrivial ↥((CFSG.perfectResidual ↥H).map
        (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))) := IsSimpleGroup.toNontrivial
    apply (nontrivial_iff_ne_bot _).mp hS1
    have hperf : ⁅(CFSG.perfectResidual ↥H).map
        (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)),
        (CFSG.perfectResidual ↥H).map (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))⁆ =
        (CFSG.perfectResidual ↥H).map (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)) := by
      rw [← map_commutator, Subgroup.isPerfect_iff.mp hYp]
    rw [← hperf]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => ?_
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hc.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hcen := center_eq_of_odd_kernel CFSG.SectionRank.oddKernelCentralization hbasic.2.2.1.1
    hYn hYp hRJ hJnil hJodd pCore_map_eq_inf_of_normal
    (layer_eq_top_center_eq_bot_of_isSimpleGroup hnaS)
  have hq : CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H) ≤
      (CFSG.perfectResidual ↥H ⊓ kerIn ((H ⊓ M).subgroupOf H) ⊤).subgroupOf
        (CFSG.perfectResidual ↥H) := by
    intro y hy
    have h1 : (y : ↥H) ∈ CFSG.perfectResidual ↥H ⊓ CFSG.Open.pCore 2 ↥H := by
      rw [← pCore_map_eq_inf_of_normal]
      exact mem_map_of_mem _ hy
    exact mem_inf.mpr ⟨y.2, hRJ (mem_inf.mp h1).2⟩
  obtain ⟨eC⟩ := nonempty_quotient_center_equiv hq hcen.1
  obtain ⟨e1⟩ := nonempty_quotient_pCore_map_equiv H (CFSG.perfectResidual ↥H)
  have e2 : (↥(CFSG.perfectResidual ↥H) ⧸ CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H)) ≃*
      (↥(CFSG.perfectResidual ↥H) ⧸ CFSG.pCore 2 ↥(CFSG.perfectResidual ↥H)) :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open _ 2).symm
  have h5 := qt13Five_of_mulEquiv (e2.trans e1).symm h5a
  have hS1 : Nontrivial ↥((CFSG.perfectResidual ↥H).map
      (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))) := IsSimpleGroup.toNontrivial
  rcases card_center_of_qt13Five h5 (exists_mul_ne_of_quotient_center eC) with hZ | ⟨hZ3, ⟨e6⟩⟩
  · left
    rw [hcen.1, hZ, Subgroup.card_bot]
  · right
    exact ⟨by rw [hcen.1, hZ3], ⟨eC.symm.trans e6⟩⟩

theorem minimal_escaping_single_factor_models
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
    ((CFSG.perfectResidual ↥H ⊓ kerIn ((H ⊓ M).subgroupOf H) ⊤).subgroupOf
        (CFSG.perfectResidual ↥H)).map
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H))) = ⊥ ∧
      kerIn ((H ⊓ M).subgroupOf H) ⊤ = CFSG.Open.pCore 2 ↥H ∧
      IsSimpleGroup (↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
        CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype)) ∧
      (∃ a b : ↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
        CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype), a * b ≠ b * a) ∧
      (Nonempty (↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
          CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype) ≃*
            alternatingGroup (Fin 5)) ∨
        CFSG.Blueprint.LieModel (↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
          CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype)) .PSL 3 2 1 ∨
        CFSG.Blueprint.LieModel (↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
          CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype)) .PSU 3 3 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA6 := nq_original_HY_alt6_central_quotient_excluded_of_normalizer h hTI hW hH₀ hTH₀ hTH
    hHH₀ hHM hmin
  have hC1 : ((CFSG.perfectResidual ↥H ⊓ kerIn ((H ⊓ M).subgroupOf H) ⊤).subgroupOf
      (CFSG.perfectResidual ↥H)).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H))) = ⊥ := by
    rcases minimal_escaping_single_factor_center hD h37 hA7u hA7n hO hN hP hI h1323 hrig h hTI
      hW hH₀ hTH₀ hTH hHH₀ hHM hmin with h1 | ⟨-, ⟨e6⟩⟩
    · exact Subgroup.card_eq_one.mp h1
    · exact (hA6.false e6).elim
  obtain ⟨-, -, -, -, h5a⟩ := minimal_escaping_single_factor hD h37 hA7u hA7n hO hN hP hI h1323
    hrig h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  have hbasic := minimal_escaping_basic h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨hT'syl, hTn', hT'X', hX'lt, hmax', hns'⟩ :=
    minimal_escaping_abstract h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨⟨hRJ, -⟩, ⟨hJnil, hJodd, -⟩, -⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hT'syl hTn' hT'X' hX'lt hmax'
  obtain ⟨-, hYT, -, hYp, hYc⟩ :=
    perfectResidual_minimal_structure hT'syl hTn' hT'X' hX'lt hmax' hns'
  have := hYc
  have hYn : (CFSG.perfectResidual ↥H).Normal := inferInstance
  have hJR : kerIn ((H ⊓ M).subgroupOf H) ⊤ = CFSG.Open.pCore 2 ↥H := by
    refine le_antisymm ?_ hRJ
    refine (kerIn_le_pCore_sup (T := T.subgroupOf H) hT'syl.2.1 hYT hJodd).trans
      (sup_le le_rfl fun x hx => ?_)
    have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H))
        (⟨x, (mem_inf.mp hx).1⟩ : ↥(CFSG.perfectResidual ↥H)) ∈
        ((CFSG.perfectResidual ↥H ⊓ kerIn ((H ⊓ M).subgroupOf H) ⊤).subgroupOf
          (CFSG.perfectResidual ↥H)).map
            (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H))) :=
      mem_map_of_mem _ (show (⟨x, (mem_inf.mp hx).1⟩ : ↥(CFSG.perfectResidual ↥H)) ∈
        (CFSG.perfectResidual ↥H ⊓ kerIn ((H ⊓ M).subgroupOf H) ⊤).subgroupOf
          (CFSG.perfectResidual ↥H) from hx)
    rw [hC1, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := mem_map_of_mem (CFSG.perfectResidual ↥H).subtype h1
    rw [pCore_map_eq_inf_of_normal] at h2
    exact (mem_inf.mp h2).2
  have hnaS : ∃ a b : ↥((CFSG.perfectResidual ↥H).map
      (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))), a * b ≠ b * a := by
    refine exists_mul_ne_of_not_isMulCommutative fun hc => ?_
    have hS1 : Nontrivial ↥((CFSG.perfectResidual ↥H).map
        (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))) := IsSimpleGroup.toNontrivial
    apply (nontrivial_iff_ne_bot _).mp hS1
    have hperf : ⁅(CFSG.perfectResidual ↥H).map
        (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)),
        (CFSG.perfectResidual ↥H).map (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))⁆ =
        (CFSG.perfectResidual ↥H).map (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)) := by
      rw [← map_commutator, Subgroup.isPerfect_iff.mp hYp]
    rw [← hperf]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => ?_
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hc.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hcen := center_eq_of_odd_kernel CFSG.SectionRank.oddKernelCentralization hbasic.2.2.1.1
    hYn hYp hRJ hJnil hJodd pCore_map_eq_inf_of_normal
    (layer_eq_top_center_eq_bot_of_isSimpleGroup hnaS)
  have hq : CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H) ≤
      (CFSG.perfectResidual ↥H ⊓ kerIn ((H ⊓ M).subgroupOf H) ⊤).subgroupOf
        (CFSG.perfectResidual ↥H) := by
    intro y hy
    have h1 : (y : ↥H) ∈ CFSG.perfectResidual ↥H ⊓ CFSG.Open.pCore 2 ↥H := by
      rw [← pCore_map_eq_inf_of_normal]
      exact mem_map_of_mem _ hy
    exact mem_inf.mpr ⟨y.2, hRJ (mem_inf.mp h1).2⟩
  obtain ⟨eC⟩ := nonempty_quotient_center_equiv hq hcen.1
  have hZ : center (↥(CFSG.perfectResidual ↥H) ⧸ CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H)) =
      ⊥ := hcen.1.symm.trans hC1
  have eE : (↥(CFSG.perfectResidual ↥H) ⧸ CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H)) ≃*
      ↥((CFSG.perfectResidual ↥H).map (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eC
  obtain ⟨e1⟩ := nonempty_quotient_pCore_map_equiv H (CFSG.perfectResidual ↥H)
  have e2 : (↥(CFSG.perfectResidual ↥H) ⧸ CFSG.Open.pCore 2 ↥(CFSG.perfectResidual ↥H)) ≃*
      (↥(CFSG.perfectResidual ↥H) ⧸ CFSG.pCore 2 ↥(CFSG.perfectResidual ↥H)) :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open _ 2).symm
  set eA := ((e2.trans e1).symm.trans eE) with heA
  have hsA : IsSimpleGroup (↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
      CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype)) := eA.isSimpleGroup
  have hnaA : ∃ a b : ↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
      CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnaS
    refine ⟨eA.symm a, eA.symm b, fun h' => hab ?_⟩
    rw [← map_mul, ← map_mul] at h'
    exact eA.symm.injective h'
  refine ⟨hC1, hJR, hsA, hnaA, ?_⟩
  rcases h5a with h5 | hL | h6 | ⟨-, hc3, -⟩ | hU
  · exact Or.inl h5
  · exact Or.inr (Or.inl hL)
  · obtain ⟨e6⟩ := h6
    exact (hA6.false (eA.symm.trans e6)).elim
  · exfalso
    rw [center_eq_bot_of_isSimpleGroup hnaA, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  · exact Or.inr (Or.inr hU)

end CFSG.Quasithin.H13.NQCore
