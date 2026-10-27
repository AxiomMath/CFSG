module

public import CFSG.Quasithin.H13.NQRigidModule
public import CFSG.Quasithin.H13.NQSetupExplicitModule
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderModule

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open Equiv
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open CFSG.QuasithinUnique.Setup.Offender (commSub commGL fixGL)
open CFSG.Quasithin.H13.NQSetup (QTNQNaturalFour QTNQNaturalThreeDouble
  QTNQNaturalThreeExtension ExplicitNaturalFour ExplicitDeletedFive ExplicitNaturalThreeDouble
  ExplicitNaturalThreeExtension)
open scoped IsMulCommutative commutatorElement

section Action

variable {G : Type} [Group G]

@[expose] noncomputable def elemAction (U : Subgroup G) [IsElementaryAbelian 2 U] :
    normalizer (U : Set G) →* (Additive U ≃ₗ[ZMod 2] Additive U) :=
  (NQSetup.mulAutLinear 2 U).comp U.normalizerMonoidHom

end Action

section QTNQ

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem qtnqU_isElementaryAbelian (h : QTNQ T L M) : IsElementaryAbelian 2 (qtnqU L M) :=
  (NQTerm.nonquasisimple_normalizer_internal_module_properties h).2.2.2.2.1.2.2.2

theorem le_normalizer_qtnqU (h : QTNQ T L M) : M ≤ normalizer (qtnqU L M : Set G) := by
  obtain ⟨-, -, -, -, ⟨-, hUM, hUn, -⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  exact (normal_subgroupOf_iff_le_normalizer hUM).mp hUn

@[expose] noncomputable def qtnqAction (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)] :
    M →* (Additive (qtnqU L M) ≃ₗ[ZMod 2] Additive (qtnqU L M)) :=
  (elemAction (qtnqU L M)).comp (inclusion (le_normalizer_qtnqU h))

@[expose] noncomputable def qtnqS (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)] :
    Subgroup (Additive (qtnqU L M) ≃ₗ[ZMod 2] Additive (qtnqU L M)) :=
  (L.subgroupOf M).map (qtnqAction h)

theorem mem_qtnqS (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)]
    {s : Additive (qtnqU L M) ≃ₗ[ZMod 2] Additive (qtnqU L M)} :
    s ∈ qtnqS h ↔ ∃ l : L, qtnqAction h ⟨l, h.l_le l.2⟩ = s := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨⟨l, h.l_le l.2⟩, l.2, rfl⟩

@[expose] noncomputable def qtnqLToS (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)] :
    L →* qtnqS h :=
  ((qtnqAction h).comp (inclusion h.l_le)).codRestrict (qtnqS h)
    (fun l => (mem_qtnqS h).mpr ⟨l, rfl⟩)

theorem qtnqLToS_surjective (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)] :
    Function.Surjective (qtnqLToS h) := by
  rintro ⟨s, hs⟩
  obtain ⟨l, rfl⟩ := (mem_qtnqS h).mp hs
  exact ⟨l, rfl⟩

@[expose] noncomputable def qtnqSEquiv (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)]
    (hfaith : ∀ l : L, (∀ x ∈ qtnqU L M, (l : G) * x * (l : G)⁻¹ = x) →
      l ∈ CFSG.solvableRadical L) :
    (L ⧸ CFSG.solvableRadical L) ≃* qtnqS h :=
  (QuotientGroup.quotientMulEquivOfEq (by
    ext l
    rw [MonoidHom.mem_ker]
    constructor
    · intro hl
      apply Subtype.ext
      apply LinearEquiv.ext
      intro e
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : G) * ((e.toMul : qtnqU L M) : G) * (l : G)⁻¹ = (e.toMul : qtnqU L M)
      rw [NQSetup.radical_commute_qtnqVc h hl (NQSetup.qtnqU_le_qtnqVc h (e.toMul).2),
        mul_inv_cancel_right]
    · intro hl
      refine hfaith l fun x hx => ?_
      have h1 := congrArg (fun s : qtnqS h =>
        ((((s : Additive (qtnqU L M) ≃ₗ[ZMod 2] Additive (qtnqU L M))
          (Additive.ofMul (⟨x, hx⟩ : qtnqU L M))).toMul : qtnqU L M) : G)) hl
      exact h1)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (qtnqLToS_surjective h))

theorem coe_qtnqSEquiv_mk (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)]
    (hfaith : ∀ l : L, (∀ x ∈ qtnqU L M, (l : G) * x * (l : G)⁻¹ = x) →
      l ∈ CFSG.solvableRadical L) (l : L) :
    ((qtnqSEquiv h hfaith (l : L ⧸ CFSG.solvableRadical L) : qtnqS h) :
      Additive (qtnqU L M) ≃ₗ[ZMod 2] Additive (qtnqU L M)) = qtnqAction h ⟨l, h.l_le l.2⟩ :=
  rfl

end QTNQ

section Faithful

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem sum_missing_eq_zero {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 5)
    (i : Ω) : ∑ j, (if j = i then (0 : ZMod 2) else 1) = 0 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter fun j : Ω => ¬ j = i).card = 4 := by
    rw [Finset.filter_ne' Finset.univ i, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, hΩ]
  rw [hcard]
  decide

theorem eq_one_of_permAct_eq {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 5)
    (σ : Perm Ω) (hσ : ∀ v ∈ evenWeight Ω, permAct σ v = v) : σ = 1 := by
  ext i
  set v : Ω → ZMod 2 := fun j => if j = i then 0 else 1 with hv
  have hvmem : v ∈ evenWeight Ω := sum_missing_eq_zero hΩ i
  have h1 : v (σ.symm (σ i)) = v (σ i) := congrFun (hσ v hvmem) (σ i)
  rw [Equiv.symm_apply_apply] at h1
  change σ i = i
  by_contra hne
  have h2 : v i = 0 := by simp [hv]
  have h3 : v (σ i) = 1 := by simp [hv, hne]
  rw [h2, h3] at h1
  exact absurd h1 (by decide)

omit [Finite G] in
theorem mem_radical_of_map_eq_one {L : Subgroup G} {Γ : Type*} [Group Γ]
    (β : (L ⧸ CFSG.solvableRadical L) ≃* Γ) {l : L}
    (hl : β (l : L ⧸ CFSG.solvableRadical L) = 1) : l ∈ CFSG.solvableRadical L := by
  rw [← QuotientGroup.eq_one_iff, ← map_one β.symm, ← hl, MulEquiv.symm_apply_apply]

omit [Finite G] in
theorem faithful_of_qtnqExplicitModule (hmod : QTNQExplicitModule L M) :
    ∀ l : L, (∀ x ∈ qtnqU L M, (l : G) * x * (l : G)⁻¹ = x) → l ∈ CFSG.solvableRadical L := by
  intro l hl
  have hfix : ∀ x : qtnqU L M, (x : G) = (l : G) * x * (l : G)⁻¹ := fun x => (hl x x.2).symm
  rcases hmod with ⟨k, _, _, -, V, _, _, -, β, φ, hsurj, hequiv, -⟩ |
      ⟨Ω, _, _, hΩ, β, θ, hθ⟩ | ⟨V, _, _, -, β, ψ, hψ⟩ | ⟨V, _, _, -, β, φ, hsurj, hequiv, -⟩
  · refine mem_radical_of_map_eq_one β (SpecialLinearGroup.ext _ _ fun v => ?_)
    obtain ⟨e, rfl⟩ := hsurj v
    have h1 := hequiv l e.toMul e.toMul (hfix e.toMul)
    exact h1.symm
  · refine mem_radical_of_map_eq_one β (Subtype.ext (eq_one_of_permAct_eq hΩ _ fun v hv => ?_))
    obtain ⟨e, he⟩ := θ.surjective ⟨v, hv⟩
    have h1 := hθ l e.toMul e.toMul (hfix e.toMul)
    simp only [ofMul_toMul] at h1
    rw [he] at h1
    exact h1.symm
  · refine mem_radical_of_map_eq_one β (LinearEquiv.ext fun v => ?_)
    obtain ⟨e, he⟩ := ψ.surjective (v, 0)
    have h1 := hψ l e.toMul e.toMul (hfix e.toMul)
    simp only [ofMul_toMul] at h1
    rw [he] at h1
    exact (congrArg Prod.fst h1).symm
  · refine mem_radical_of_map_eq_one β (LinearEquiv.ext fun v => ?_)
    obtain ⟨e, rfl⟩ := hsurj v
    have h1 := hequiv l e.toMul e.toMul (hfix e.toMul)
    exact h1.symm

end Faithful

section Transport

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem exists_mk_of_qtnqS (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)]
    (hfaith : ∀ l : L, (∀ x ∈ qtnqU L M, (l : G) * x * (l : G)⁻¹ = x) →
      l ∈ CFSG.solvableRadical L) (s : qtnqS h) :
    ∃ l : L, (qtnqSEquiv h hfaith).symm s = (l : L ⧸ CFSG.solvableRadical L) ∧
      (s : Additive (qtnqU L M) ≃ₗ[ZMod 2] Additive (qtnqU L M)) =
        qtnqAction h ⟨l, h.l_le l.2⟩ := by
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective ((qtnqSEquiv h hfaith).symm s)
  refine ⟨l, hl.symm, ?_⟩
  have h1 : s = qtnqSEquiv h hfaith (l : L ⧸ CFSG.solvableRadical L) := by
    rw [hl, MulEquiv.apply_symm_apply]
  rw [h1, coe_qtnqSEquiv_mk]

theorem explicitNaturalFour_of_qtnq (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)]
    (ha : QTNQNaturalFour L M) : ExplicitNaturalFour (qtnqS h) := by
  have hfaith := faithful_of_qtnqExplicitModule (Or.inl ha)
  obtain ⟨k, _, _, hk, V, _, _, hV, β, φ, hsurj, hequiv, hker⟩ := ha
  refine ⟨k, _, _, hk, V, _, _, hV, (qtnqSEquiv h hfaith).symm.trans β, φ, hsurj, ?_, ?_⟩
  · intro s e
    obtain ⟨l, hl, hs⟩ := exists_mk_of_qtnqS h hfaith s
    rw [MulEquiv.trans_apply, hl, hs]
    exact hequiv l e.toMul _ rfl
  · intro s hs e he
    obtain ⟨l, rfl⟩ := (mem_qtnqS h).mp hs
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hker l e.toMul he

theorem explicitDeletedFive_of_qtnq (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)]
    (hb : QTNQDeletedFive L M) : ExplicitDeletedFive (qtnqS h) := by
  have hfaith := faithful_of_qtnqExplicitModule (Or.inr (Or.inl hb))
  obtain ⟨Ω, _, _, hΩ, β, θ, hθ⟩ := hb
  let θl : Additive (qtnqU L M) ≃ₗ[ZMod 2] evenWeight Ω :=
    { toFun := θ, invFun := θ.symm, map_add' := θ.map_add,
      map_smul' := fun c x => by
        have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
        rcases hc c with rfl | rfl
        · rw [zero_smul, RingHom.id_apply, zero_smul, map_zero]
        · rw [one_smul, RingHom.id_apply, one_smul],
      left_inv := θ.symm_apply_apply, right_inv := θ.apply_symm_apply }
  refine ⟨Ω, _, _, hΩ, (qtnqSEquiv h hfaith).symm.trans β, θl, ?_⟩
  intro s e
  obtain ⟨l, hl, hs⟩ := exists_mk_of_qtnqS h hfaith s
  rw [MulEquiv.trans_apply, hl, hs]
  exact hθ l e.toMul _ rfl

theorem explicitNaturalThreeDouble_of_qtnq (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)]
    (hc : QTNQNaturalThreeDouble L M) : ExplicitNaturalThreeDouble (qtnqS h) := by
  have hfaith := faithful_of_qtnqExplicitModule (Or.inr (Or.inr (Or.inl hc)))
  obtain ⟨V, _, _, hV, β, ψ, hψ⟩ := hc
  let ψl : Additive (qtnqU L M) ≃ₗ[ZMod 2] V × V :=
    { toFun := ψ, invFun := ψ.symm, map_add' := ψ.map_add,
      map_smul' := fun c x => ZMod.map_smul ψ.toAddMonoidHom c x,
      left_inv := ψ.symm_apply_apply, right_inv := ψ.apply_symm_apply }
  refine ⟨V, _, _, hV, (qtnqSEquiv h hfaith).symm.trans β, ψl, ?_⟩
  intro s e
  obtain ⟨l, hl, hs⟩ := exists_mk_of_qtnqS h hfaith s
  rw [MulEquiv.trans_apply, hl, hs]
  exact hψ l e.toMul _ rfl

theorem explicitNaturalThreeExtension_of_qtnq (h : QTNQ T L M)
    [IsElementaryAbelian 2 (qtnqU L M)] (hc : QTNQNaturalThreeExtension L M) :
    ExplicitNaturalThreeExtension (qtnqS h) := by
  have hfaith := faithful_of_qtnqExplicitModule (Or.inr (Or.inr (Or.inr hc)))
  obtain ⟨V, _, _, hV, β, φ, hsurj, hequiv, hker⟩ := hc
  refine ⟨V, _, _, hV, (qtnqSEquiv h hfaith).symm.trans β, φ.toZModLinearMap 2, hsurj, ?_, ?_⟩
  · intro s e
    obtain ⟨l, hl, hs⟩ := exists_mk_of_qtnqS h hfaith s
    rw [MulEquiv.trans_apply, hl, hs]
    exact hequiv l e.toMul _ rfl
  · intro s hs e he
    obtain ⟨l, rfl⟩ := (mem_qtnqS h).mp hs
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hker l e.toMul he

theorem explicitModule_of_qtnqExplicitModule (h : QTNQ T L M)
    [IsElementaryAbelian 2 (qtnqU L M)] (hmod : QTNQExplicitModule L M) :
    ExplicitNaturalFour (qtnqS h) ∨ ExplicitDeletedFive (qtnqS h) ∨
      ExplicitNaturalThreeDouble (qtnqS h) ∨ ExplicitNaturalThreeExtension (qtnqS h) := by
  rcases hmod with ha | hb | hc | hc
  · exact Or.inl (explicitNaturalFour_of_qtnq h ha)
  · exact Or.inr (Or.inl (explicitDeletedFive_of_qtnq h hb))
  · exact Or.inr (Or.inr (Or.inl (explicitNaturalThreeDouble_of_qtnq h hc)))
  · exact Or.inr (Or.inr (Or.inr (explicitNaturalThreeExtension_of_qtnq h hc)))

end Transport

section Commutator

variable {G : Type} [Group G]

@[expose] def subspaceOf (K : Subgroup G) [IsElementaryAbelian 2 K] (W : Subgroup G) :
    Submodule (ZMod 2) (Additive K) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (W.subgroupOf K))

theorem mem_subspaceOf {K : Subgroup G} [IsElementaryAbelian 2 K] {W : Subgroup G}
    {e : Additive K} : e ∈ subspaceOf K W ↔ ((e.toMul : K) : G) ∈ W := Iff.rfl

theorem ofMul_mem_commSub_iff {K W L : Subgroup G} [IsElementaryAbelian 2 K] (hWK : W ≤ K)
    (hLK : L ≤ normalizer (K : Set G)) (x : K) :
    Additive.ofMul x ∈ commSub ((elemAction K).comp (inclusion hLK)) ⊤ (subspaceOf K W) ↔
      (x : G) ∈ ⁅W, L⁆ := by
  classical
  set ρ := (elemAction K).comp (inclusion hLK) with hρ
  have hsmul : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  constructor
  · intro hx
    let P : Submodule (ZMod 2) (Additive K) :=
      { carrier := {e | ((e.toMul : K) : G) ∈ ⁅W, L⁆}
        add_mem' := fun {a b} ha hb => ⁅W, L⁆.mul_mem ha hb
        zero_mem' := ⁅W, L⁆.one_mem
        smul_mem' := fun c e he => by
          rcases hsmul c with rfl | rfl
          · rw [zero_smul]
            exact ⁅W, L⁆.one_mem
          · rw [one_smul]
            exact he }
    have hle : commSub ρ ⊤ (subspaceOf K W) ≤ P := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, -, e, he, rfl⟩
      change ((ρ l e - e).toMul : G) ∈ ⁅W, L⁆
      have h1 : ((ρ l e - e).toMul : G) =
          (l : G) * (e.toMul : G) * (l : G)⁻¹ * (e.toMul : G)⁻¹ := by
        rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
        rfl
      rw [h1, ← commutatorElement_def, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator l.2 (mem_subspaceOf.mp he)
    exact hle hx
  · intro hx
    let Q : Subgroup G :=
      { carrier := {g | ∃ hg : g ∈ K, Additive.ofMul (⟨g, hg⟩ : K) ∈
          commSub ρ ⊤ (subspaceOf K W)}
        mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
          ⟨K.mul_mem ha hb, (commSub ρ ⊤ (subspaceOf K W)).add_mem ha' hb'⟩
        one_mem' := ⟨K.one_mem, (commSub ρ ⊤ (subspaceOf K W)).zero_mem⟩
        inv_mem' := fun {a} ⟨ha, ha'⟩ =>
          ⟨K.inv_mem ha, (commSub ρ ⊤ (subspaceOf K W)).neg_mem ha'⟩ }
    have hle : ⁅W, L⁆ ≤ Q := by
      rw [Subgroup.commutator_le]
      intro w hw l hl
      have hwK : w ∈ K := hWK hw
      have hlw : (l : G) * w⁻¹ * l⁻¹ ∈ K :=
        (mem_normalizer_iff.mp (hLK hl) w⁻¹).mp (K.inv_mem hwK)
      have hc : ⁅w, l⁆ = w * ((l : G) * w⁻¹ * l⁻¹) := by
        rw [commutatorElement_def]
        group
      have hcK : ⁅w, l⁆ ∈ K := hc ▸ K.mul_mem hwK hlw
      refine ⟨hcK, ?_⟩
      have h1 : Additive.ofMul (⟨⁅w, l⁆, hcK⟩ : K) =
          -(ρ ⟨l, hl⟩ (Additive.ofMul ⟨w, hwK⟩) - Additive.ofMul ⟨w, hwK⟩) := by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [toMul_neg, toMul_sub, Subgroup.coe_inv, Subgroup.coe_div, div_eq_mul_inv]
        change ⁅w, l⁆ = ((l : G) * w * (l : G)⁻¹ * w⁻¹)⁻¹
        rw [commutatorElement_def]
        group
      rw [h1]
      exact (commSub ρ ⊤ (subspaceOf K W)).neg_mem
        (CFSG.QuasithinUnique.Setup.Offender.mem_commSub_of (mem_top _) (mem_subspaceOf.mpr hw))
    obtain ⟨hxK, hx'⟩ := hle hx
    exact hx'

end Commutator

section Idempotent

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem qtnqVc_isElementaryAbelian (_h : QTNQ T L M) : IsElementaryAbelian 2 (qtnqVc M) := by
  obtain ⟨-, -, -, -, -, -, -, -, hVel, -⟩ :=
    qt_prime_reduced_aggregate_characteristic_maximal (↥M) 2
  exact BlueprintB2.isElementaryAbelian_map hVel _

theorem le_normalizer_qtnqVc (h : QTNQ T L M) : M ≤ normalizer (qtnqVc M : Set G) := by
  obtain ⟨-, hchar, -⟩ := NQTerm.nonquasisimple_normalizer_internal_module_properties h
  exact le_normalizer.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

theorem commutator_qtnqU_eq (h : QTNQ T L M) : ⁅qtnqU L M, L⁆ = qtnqU L M := by
  classical
  have hVcel := qtnqVc_isElementaryAbelian h
  have hLVc : L ≤ normalizer (qtnqVc M : Set G) := h.l_le.trans (le_normalizer_qtnqVc h)
  have hUVc : qtnqU L M ≤ qtnqVc M := NQSetup.qtnqU_le_qtnqVc h
  set ρ := (elemAction (qtnqVc M)).comp (inclusion hLVc) with hρ
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  have hperf : Group.IsPerfect L := ⟨by rw [_root_.commutator_def]; exact hLC.2.1⟩
  have hidem := CFSG.QuasithinUnique.Setup.Offender.commSub_commSub_of_perfect ρ hperf
  have htop : subspaceOf (qtnqVc M) (qtnqVc M) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    exact mem_subspaceOf.mpr (e.toMul).2
  have hcomm1 : commSub ρ ⊤ ⊤ = subspaceOf (qtnqVc M) (qtnqU L M) := by
    ext e
    rw [← htop, mem_subspaceOf]
    exact ofMul_mem_commSub_iff le_rfl hLVc e.toMul
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro u hu l hl
    have hlu : (l : G) * u⁻¹ * l⁻¹ ∈ qtnqU L M :=
      (mem_normalizer_iff.mp (le_normalizer_qtnqU h (h.l_le hl)) u⁻¹).mp ((qtnqU L M).inv_mem hu)
    rw [commutatorElement_def, show u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) by group]
    exact (qtnqU L M).mul_mem hu hlu
  · intro u hu
    have h1 : Additive.ofMul (⟨u, hUVc hu⟩ : qtnqVc M) ∈ commSub ρ ⊤ ⊤ := by
      rw [hcomm1]
      exact mem_subspaceOf.mpr hu
    rw [← hidem, hcomm1] at h1
    exact (ofMul_mem_commSub_iff hUVc hLVc ⟨u, hUVc hu⟩).mp h1

theorem commGL_qtnqS_eq_top (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)] :
    commGL (qtnqS h) ⊤ = ⊤ := by
  classical
  have hLU : L ≤ normalizer (qtnqU L M : Set G) := h.l_le.trans (le_normalizer_qtnqU h)
  set ρ := (elemAction (qtnqU L M)).comp (inclusion hLU) with hρ
  have htop : subspaceOf (qtnqU L M) (qtnqU L M) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    exact mem_subspaceOf.mpr (e.toMul).2
  have hle : commSub ρ ⊤ ⊤ ≤ commGL (qtnqS h) ⊤ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, -, e, -, rfl⟩
    exact Submodule.subset_span ⟨qtnqAction h ⟨l, h.l_le l.2⟩, (mem_qtnqS h).mpr ⟨l, rfl⟩, e,
      Submodule.mem_top, rfl⟩
  rw [eq_top_iff]
  intro e _
  apply hle
  rw [← htop]
  have h1 : ((e.toMul : qtnqU L M) : G) ∈ ⁅qtnqU L M, L⁆ := by
    rw [commutator_qtnqU_eq h]
    exact (e.toMul).2
  exact (ofMul_mem_commSub_iff le_rfl hLU e.toMul).mpr h1

end Idempotent

end CFSG.Quasithin.H13.NQRigid
