module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldAutNL
import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
import CFSG.RankThree.Chevalley.SteinbergBTEvenE6Noninner
import CFSG.RankThree.PartOne.KE.OddE6NoninnerCore

public section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley.SteinbergBT (orderOf_entrywiseAdjointAut not_commute_fixedFieldImage)
open CFSG.ComponentClassification.UnbalancedCatalog (mem_zpowers_of_fixed)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.RankThree.Chevalley (exists_mulEquiv_adjointGroup_of_untwisted
  Chevalley_exceptional_models_order_divisible_by_three
  even_E6_noninner_large_prime_field_descent_and_local_core_trivial
  odd_E7_noninner_odd_prime_field_descent_and_local_core_trivial)
open CFSG.RankThree.PartOne.KE (odd_E6_noninner_large_prime_field_descent_and_local_core_trivial)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem fixedClauses_of_J_simple_stabilizer
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hCs : IsSimpleGroup (adjointGroup τ K))
    (hCn : ∃ a b : adjointGroup τ K, a * b ≠ b * a)
    (hpC : ¬ p ∣ Nat.card (adjointGroup τ K)) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hJs : IsSimpleGroup (fixedFieldImage τ σ))
    (hstab : ∀ β : MulAut (adjointGroup τ K),
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → β j = j) →
        β ∈ Subgroup.zpowers (entrywiseAdjointAut τ σ))
    (hNL : FStarSimple (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) →
      NonLocalized (signalizerFixedSubgroup (entrywiseAdjointAut τ σ))) :
    FixedClauses p (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have : IsSimpleGroup (fixedFieldImage τ σ) := hJs
  have hJΓ : fixedFieldImage τ σ ≤ entrywiseFixedGroup τ σ := fixedFieldImage_le
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun j hj => (hJΓ hj).1
  let eJC : (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ≃* fixedFieldImage τ σ :=
    Subgroup.subgroupOfEquivOfLe hJC
  have hJs' : IsSimpleGroup ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) :=
    eJC.isSimpleGroup
  have hJn : ∃ x y : (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K), x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply not_commute_fixedFieldImage τ.rank_pos σ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hmemΓ : ∀ g : adjointGroup τ K,
      g ∈ (entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ K) ↔
        entrywiseAdjointAut τ σ g = g := fun g => by
    rw [Subgroup.mem_subgroupOf, mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext ((coe_entrywiseAdjointAut τ σ g).trans h)
    · intro h
      exact ⟨g.2, (coe_entrywiseAdjointAut τ σ g).symm.trans (congrArg Subtype.val h)⟩
  have hJN : (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ≤
      (entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ K) := fun g hg => hJΓ hg
  have hΓnorm : entrywiseFixedGroup τ σ ≤
      Subgroup.normalizer (fixedFieldImage τ σ : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 fixedFieldImage_normal
  have hJnorm : (((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).subgroupOf
      ((entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ K))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJN).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hΓnorm hg) (h : ModGL τ K)
  have hJst : ∀ β : MulAut (adjointGroup τ K),
      (∀ x ∈ (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K), β x = x) →
        β ∈ Subgroup.zpowers (entrywiseAdjointAut τ σ) := fun β hβ =>
    hstab β fun j hj => hβ j (Subgroup.mem_subgroupOf.2 hj)
  exact fixedClauses_of_simple_normal_stabilizer hp hCs hCn hpC
    (by rw [orderOf_entrywiseAdjointAut τ.rank_pos σ, hσ]) hJN hJnorm hJs' hJn
    (fun t => (hmemΓ t).symm) hJst hNL

theorem isSimpleGroup_fixedFieldImage_of_quasisimple
    {τ : Tag} {K : Type} [Field K]
    (σ : K ≃+* K) (hq : CFSG.IsQuasisimple (adjointGroup τ (fixSubfield σ))) :
    IsSimpleGroup (fixedFieldImage τ σ) :=
  CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
    ((Subgroup.equivMapOfInjective (adjointGroup τ (fixSubfield σ)) _
      (baseChangeGL_injective (τ := τ) (fixSubfield σ).subtype)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot_field τ _)).trans
        QuotientGroup.quotientBot).symm)

theorem fieldClauses_E6
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hsC : IsSimpleGroup (adjointGroup .E6 K)) (hnC : ∃ a b : adjointGroup .E6 K, a * b ≠ b * a)
    (hpC : ¬ p ∣ Nat.card (adjointGroup .E6 K))
    (hNL : ChevalleySubfieldNL .E6 K p) : FieldClauses p (adjointGroup .E6 K) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  rintro ⟨f₁, hf₁⟩
  have hout := not_mem_inner_range_of_orderOf hpC hf₁
  have hB : orderOf (⟨f₁, Subgroup.mem_top f₁⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup .E6 K)))) = p := by
    rw [Subgroup.orderOf_mk, hf₁]
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, orderOf σ = p := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
      obtain ⟨⟨σ, -, hσ, -⟩, -⟩ :=
        even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hK Θ hΘ hp hp3 ⊤
          le_top ⟨f₁, Subgroup.mem_top f₁⟩ hout hB
      exact ⟨σ, hσ⟩
    · obtain ⟨-, ⟨σ, -, hσ, -⟩, -⟩ :=
        odd_E6_noninner_large_prime_field_descent_and_local_core_trivial hℓ hℓ2 hf K hK hp hp3 ⊤
          le_top ⟨f₁, Subgroup.mem_top f₁⟩ hout hB
      exact ⟨σ, hσ⟩
  have hord : orderOf (entrywiseAdjointAut .E6 σ) = p := by
    rw [orderOf_entrywiseAdjointAut Tag.E6.rank_pos σ, hσ]
  refine ⟨entrywiseAdjointAut .E6 σ, hord, fixedClauses_of_J_simple_stabilizer hp hsC hnC hpC σ hσ
    (isSimpleGroup_fixedFieldImage_of_quasisimple σ
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 (fixSubfield σ)))
    (fun β hβ => FieldGraphFieldPointwise.mem_zpowers_of_forall_fixedFieldImage σ hβ)
    fun _ => nonLocalized_fixed_entrywiseAdjointAut σ (hNL σ hσ)⟩

theorem fieldClauses_chevalleyE6
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .E6 ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedChevalley) : FieldClauses p T := by
  have hp3 : 3 < p := by
    have h3 := Chevalley_exceptional_models_order_divisible_by_three T .E6 ℓ f hm
    have hp3 : p ≠ 3 := fun h => hpT (h ▸ h3)
    have := hp.two_le
    omega
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .E6 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .E6 K) := e.isSimpleGroup
  have hnC : ∃ a b : adjointGroup .E6 K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  have hpC : ¬ p ∣ Nat.card (adjointGroup .E6 K) := by rwa [Nat.card_congr e.toEquiv]
  exact FieldClauses.of_mulEquiv e
    (fieldClauses_E6 hadm.1 hadm.2.1 K hK hp hp3 hsC hnC hpC
      (ChevalleySubfieldNL.of_chevalley hNL (Or.inr (Or.inr (Or.inl rfl))) hsC hp hp2 hpC))

theorem odd_E7_zpowers_of_fixes
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) :
    ∀ β : MulAut (adjointGroup .E7 K),
      (∀ j : adjointGroup .E7 K, (j : ModGL .E7 K) ∈ fixedFieldImage .E7 σ → β j = j) →
        β ∈ Subgroup.zpowers (entrywiseAdjointAut .E7 σ) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hfixer⟩ :=
    CFSG.RankThree.OddE7Rational.odd_E7_rational_inner_diagonal_field_automorphism_structure hℓ
      hℓ2 hf K hK (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
      (fun c => by rw [iterateFrobenius_def, hK]) _ _ rfl rfl
  intro β hβ
  have hS := (hfixer (fixSubfield σ) _ rfl).1
  have hβS : β ∈ ((fixingSubgroup (MulAut (adjointGroup Tag.E7 K))
      {j : adjointGroup Tag.E7 K | (j : ModGL Tag.E7 K) ∈
        (adjointGroup Tag.E7 (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype)} :
          Subgroup (MulAut (adjointGroup Tag.E7 K))) : Set (MulAut (adjointGroup Tag.E7 K))) :=
    (mem_fixingSubgroup_iff _).2 fun j hj => hβ j hj
  rw [hS] at hβS
  obtain ⟨σ', rfl⟩ := hβS
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_fixed (σ := σ) (φ := σ'.toRingEquiv) fun c hc =>
      σ'.commutes (⟨c, hc⟩ : fixSubfield σ))
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  show entrywiseAdjointAut .E7 σ ^ n = entrywiseAdjointAut .E7 σ'.toRingEquiv
  rw [← hn]
  exact (map_zpow (entrywiseAdjointAutHom (τ := .E7)) σ n).symm

theorem fieldClauses_E7
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hsC : IsSimpleGroup (adjointGroup .E7 K)) (hnC : ∃ a b : adjointGroup .E7 K, a * b ≠ b * a)
    (hpC : ¬ p ∣ Nat.card (adjointGroup .E7 K))
    (hNL : ChevalleySubfieldNL .E7 K p) : FieldClauses p (adjointGroup .E7 K) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  rintro ⟨f₁, hf₁⟩
  have hout := not_mem_inner_range_of_orderOf hpC hf₁
  have hB : orderOf (⟨f₁, Subgroup.mem_top f₁⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup .E7 K)))) = p := by
    rw [Subgroup.orderOf_mk, hf₁]
  obtain ⟨-, ⟨σ, -, hσ, -⟩, -⟩ := odd_E7_noninner_odd_prime_field_descent_and_local_core_trivial
    hℓ hℓ2 hf K hK hp hp2 ⊤ le_top ⟨f₁, Subgroup.mem_top f₁⟩ hout hB
  have hord : orderOf (entrywiseAdjointAut .E7 σ) = p := by
    rw [orderOf_entrywiseAdjointAut Tag.E7.rank_pos σ, hσ]
  refine ⟨entrywiseAdjointAut .E7 σ, hord, fixedClauses_of_J_simple_stabilizer hp hsC hnC hpC σ hσ
    (isSimpleGroup_fixedFieldImage_of_quasisimple σ
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 (fixSubfield σ)))
    (odd_E7_zpowers_of_fixes hℓ hℓ2 hf K hK σ)
    fun _ => nonLocalized_fixed_entrywiseAdjointAut σ (hNL σ hσ)⟩

theorem fieldClauses_chevalleyOddE7
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .E7 ℓ f) (hℓ2 : ℓ ≠ 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedChevalley) :
    FieldClauses p T := by
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .E7 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .E7 K) := e.isSimpleGroup
  have hnC : ∃ a b : adjointGroup .E7 K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  have hpC : ¬ p ∣ Nat.card (adjointGroup .E7 K) := by rwa [Nat.card_congr e.toEquiv]
  exact FieldClauses.of_mulEquiv e
    (fieldClauses_E7 hadm.1 hℓ2 hadm.2.1 K hK hp hp2 hsC hnC hpC
      (ChevalleySubfieldNL.of_chevalley hNL (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hsC hp hp2
        hpC))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
