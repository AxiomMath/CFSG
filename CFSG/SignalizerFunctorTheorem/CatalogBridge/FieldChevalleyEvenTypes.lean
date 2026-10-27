module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyEven
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldAutNL
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE7E8AllOrders
public import CFSG.RankThree.Chevalley.SteinbergBTEvenF4AllOrders
import CFSG.RankThree.Chevalley.SteinbergBTEvenE7E8Noninner
import CFSG.RankThree.Chevalley.SteinbergBTEvenF4Noninner
import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution

public section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley.SteinbergBT (orderOf_entrywiseAdjointAut)
open CFSG.ComponentClassification.UnbalancedCatalog (ringAut_commute)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.RankThree.Chevalley (exists_mulEquiv_adjointGroup_of_untwisted
  even_E7_E8_canonical_field_centralizer_all_orders
  even_E7_E8_noninner_prime_field_descent_and_local_core_trivial
  even_F4_canonical_field_centralizer_all_orders
  even_F4_noninner_odd_prime_field_descent_and_local_core_trivial)
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem hS2_of_centralizer_inf_eq
    {τ : Tag} {K : Type} [Field K] (σ : K ≃+* K)
    (hcent : Subgroup.centralizer {entrywiseAdjointAut τ σ} ⊓
        Subgroup.centralizer ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
          (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) :
            Subgroup (MulAut (adjointGroup τ K))) : Set (MulAut (adjointGroup τ K))) =
      Subgroup.zpowers (entrywiseAdjointAut τ σ)) :
    ∀ β : MulAut (adjointGroup τ K),
      β * entrywiseAdjointAut τ σ = entrywiseAdjointAut τ σ * β →
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → β j = j) →
        β ∈ Subgroup.zpowers (entrywiseAdjointAut τ σ) := by
  intro β hcomm hfix
  rw [← hcent]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hcomm.symm
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    have h1 : β * MulAut.conj j * β⁻¹ = MulAut.conj (β j) := mulAut_mul_conj_mul_inv β j
    rw [hfix j (Subgroup.mem_subgroupOf.1 hj)] at h1
    calc MulAut.conj j * β = (β * MulAut.conj j * β⁻¹) * β := by rw [h1]
      _ = β * MulAut.conj j := by group

theorem fixedClauses_evenE78
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f p : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K)
    (hσ : orderOf σ = p)
    (hNL : FStarSimple (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) →
      NonLocalized (signalizerFixedSubgroup (entrywiseAdjointAut τ σ))) :
    FixedClauses p (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hrank : 0 < τ.rank := by
    rcases hτ with rfl | rfl <;> decide
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
    (Or.inr (Or.inr (Or.inr hτ))) hchar σ
  obtain ⟨-, -, hsimple, -, -, -, -, -, -, hcent, -⟩ :=
    even_E7_E8_canonical_field_centralizer_all_orders τ hτ hf K hK σ
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  exact fixedClauses_of_fixedFieldImage_S2 σ hσ hrank hΓJ hsimple
    (commutator_mem_inner_of_hom (fun a b => ringAut_commute a b) Θ hΘker)
    (hS2_of_centralizer_inf_eq σ hcent) hNL

theorem exists_fieldAut_evenE78
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f p : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (hp : p.Prime)
    (hpC : ¬ p ∣ Nat.card (adjointGroup τ K)) {α : MulAut (adjointGroup τ K)}
    (hα : orderOf α = p) : ∃ σ : K ≃+* K, orderOf σ = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  have hσp : Θ α ^ p = 1 := by rw [← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hσ1 : Θ α ≠ 1 := by
    intro h
    have hmem : α ∈ Θ.ker := h
    rw [hΘker] at hmem
    exact not_mem_inner_range_of_orderOf hpC hα hmem
  exact ⟨Θ α, orderOf_eq_prime hσp hσ1⟩

theorem fieldClauses_evenE78
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f p : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (hp : p.Prime)
    (hpC : ¬ p ∣ Nat.card (adjointGroup τ K))
    (hNL : ChevalleySubfieldNL τ K p) : FieldClauses p (adjointGroup τ K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hrank : 0 < τ.rank := by
    rcases hτ with rfl | rfl <;> decide
  rintro ⟨α, hα⟩
  obtain ⟨σ, hσ⟩ := exists_fieldAut_evenE78 hτ hf K hK hp hpC hα
  have hf₀ : orderOf (entrywiseAdjointAut τ σ) = p := by
    rw [orderOf_entrywiseAdjointAut hrank σ, hσ]
  exact ⟨entrywiseAdjointAut τ σ, hf₀, fixedClauses_evenE78 hτ hf K hK σ hσ
    fun _ => nonLocalized_fixed_entrywiseAdjointAut σ (hNL σ hσ)⟩

theorem fixedClauses_evenF4
    {f p : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K)
    (hσ : orderOf σ = p)
    (hNL : FStarSimple (signalizerFixedSubgroup (entrywiseAdjointAut .F4 σ)) →
      NonLocalized (signalizerFixedSubgroup (entrywiseAdjointAut .F4 σ))) :
    FixedClauses p (signalizerFixedSubgroup (entrywiseAdjointAut .F4 σ)) := by
  have hchar : ringChar K = 2 := ringChar.eq K CFSG.LieType.Ree.ReeTag.F4.prime
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (τ := .F4)
    (Or.inr (Or.inl rfl)) hchar σ
  obtain ⟨-, -, hsimple, -, -, -, -, -, -, hcent, -⟩ :=
    even_F4_canonical_field_centralizer_all_orders hf hK σ
  obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  exact fixedClauses_of_fixedFieldImage_S2 σ hσ (by decide) hΓJ hsimple
    (commutator_mem_inner_of_hom (fun a b => mul_comm a b) Θ hΘker)
    (hS2_of_centralizer_inf_eq σ hcent) hNL

theorem exists_fieldAut_evenF4
    {f p : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpC : ¬ p ∣ Nat.card (adjointGroup .F4 K))
    {α : MulAut (adjointGroup .F4 K)} (hα : orderOf α = p) : ∃ σ : K ≃+* K, orderOf σ = p := by
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α
  have hαinn := not_mem_inner_range_of_orderOf hpC hα
  obtain ⟨-, -, ⟨σ, hσ⟩, hord, -⟩ :=
    even_F4_noninner_odd_prime_field_descent_and_local_core_trivial hf hK hp hp2 ⊤
      (fun _ _ => Subgroup.mem_top _) ⟨α, Subgroup.mem_top α⟩ hαinn
      ((Subgroup.orderOf_mk α (Subgroup.mem_top α)).trans hα) x a a.2 hxa
  exact ⟨σ, (hord σ hσ).1⟩

theorem fieldClauses_chevalleyEvenF4
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {ℓ f p : ℕ} (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .F4 ℓ f) (hℓ2 : ℓ = 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedChevalley) : FieldClauses p T := by
  subst hℓ2
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .F4 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .F4 K) := e.isSimpleGroup
  have hpC : ¬ p ∣ Nat.card (adjointGroup .F4 K) := by rwa [Nat.card_congr e.toEquiv]
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime :=
    finite_field_prime_power_characteristic Nat.prime_two hadm.2.1 hK
  have hNLK := ChevalleySubfieldNL.of_chevalley hNL (Or.inr (Or.inl rfl)) hsC hp hp2 hpC
  refine FieldClauses.of_mulEquiv e ?_
  rintro ⟨α, hα⟩
  obtain ⟨σ, hσ⟩ := exists_fieldAut_evenF4 hadm.2.1 K hK hp hp2 hpC hα
  have hf₀ : orderOf (entrywiseAdjointAut .F4 σ) = p := by
    rw [orderOf_entrywiseAdjointAut (by decide) σ, hσ]
  exact ⟨_, hf₀, fixedClauses_evenF4 hadm.2.1 K hK σ hσ fun _ =>
    nonLocalized_fixed_entrywiseAdjointAut σ (hNLK σ hσ)⟩

theorem fieldClauses_chevalleyEvenE7
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {ℓ f p : ℕ} (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .E7 ℓ f) (hℓ2 : ℓ = 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedChevalley) : FieldClauses p T := by
  subst hℓ2
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .E7 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .E7 K) := e.isSimpleGroup
  have hpC : ¬ p ∣ Nat.card (adjointGroup .E7 K) := by rwa [Nat.card_congr e.toEquiv]
  exact FieldClauses.of_mulEquiv e
    (fieldClauses_evenE78 (Or.inl rfl) hadm.2.1 K hK hp hpC
      (ChevalleySubfieldNL.of_chevalley hNL (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hsC hp hp2
        hpC))

theorem fieldClauses_chevalleyEvenE8
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {ℓ f p : ℕ} (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .E8 ℓ f) (hℓ2 : ℓ = 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedChevalley) : FieldClauses p T := by
  subst hℓ2
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .E8 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .E8 K) := e.isSimpleGroup
  have hpC : ¬ p ∣ Nat.card (adjointGroup .E8 K) := by rwa [Nat.card_congr e.toEquiv]
  exact FieldClauses.of_mulEquiv e
    (fieldClauses_evenE78 (Or.inr rfl) hadm.2.1 K hK hp hpC
      (ChevalleySubfieldNL.of_chevalley hNL (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hsC hp hp2
        hpC))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
