module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
import CFSG.RankThree.Chevalley.SteinbergBMG2NoninnerLocalCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form
  entrywiseFixedGroup_eq_fixedFieldImage)


section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def g2Fixed (σ : K ≃+* K) : Subgroup (adjointGroup .G2 K) :=
  (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)

end Defs

@[expose] def SubfieldPairG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], CharP K 2 → ∀ (σ : K ≃+* K) (p : ℕ), p.Prime → 5 ≤ p →
    orderOf σ = p → ∀ g : adjointGroup .G2 K,
      (g2Fixed σ).map (MulAut.conj g).toMonoidHom ≠ g2Fixed σ →
      Subgroup.closure ((g2Fixed σ : Set (adjointGroup .G2 K)) ∪
        ((g2Fixed σ).map (MulAut.conj g).toMonoidHom : Set (adjointGroup .G2 K))) = ⊤ ∨
        ¬ p ∣ Nat.card (g2Fixed σ)

section Fixed

variable {K : Type} [Field K] [Finite K]

theorem fixedSubgroup_entrywise_eq (σ : K ≃+* K) :
    fixedSubgroup (entrywiseAdjointAut .G2 σ) = g2Fixed σ := by
  ext x
  rw [mem_fixedSubgroup, g2Fixed, Subgroup.mem_subgroupOf,
    ← entrywiseFixedGroup_eq_fixedFieldImage σ, mem_entrywiseFixedGroup]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have := congrArg Subtype.val h
    rwa [coe_entrywiseAdjointAut] at this
  · rintro ⟨-, h⟩
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact h

omit [Finite K] in
theorem g2Fixed_congr {σ τ : K ≃+* K} (h : fixSubfield σ = fixSubfield τ) :
    g2Fixed σ = g2Fixed τ := by
  unfold g2Fixed fixedFieldImage
  rw [h]

noncomputable def g2FixedEquiv (σ : K ≃+* K) :
    ↥(g2Fixed σ) ≃* adjointGroup .G2 (fixSubfield σ) :=
  (Subgroup.subgroupOfEquivOfLe
    ((entrywiseFixedGroup_eq_fixedFieldImage σ) ▸ inf_le_left)).trans
    (fixedFieldImageEquiv (τ := .G2) σ).symm

theorem eq_one_of_central_g2Fixed (σ : K ≃+* K) {x : adjointGroup .G2 K} (hx : x ∈ g2Fixed σ)
    (hc : ∀ y ∈ g2Fixed σ, x * y = y * x) : x = 1 := by
  have hz : g2FixedEquiv σ ⟨x, hx⟩ ∈ Subgroup.center (adjointGroup .G2 (fixSubfield σ)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, hy⟩ : ∃ y : ↥(g2Fixed σ), g2FixedEquiv σ y = g :=
      ⟨(g2FixedEquiv σ).symm g, by simp⟩
    rw [← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2).symm
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  have h1 : (⟨x, hx⟩ : ↥(g2Fixed σ)) = 1 := (g2FixedEquiv σ).injective (by rw [hz, map_one])
  exact congrArg Subtype.val h1

end Fixed

section Descent

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem exists_conj_mem_of_plane (hp : p.Prime) (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (E : Subgroup (MulAut (adjointGroup .G2 K))) [hE : IsElementaryAbelian p E]
    (hEc : Nat.card E = p ^ 2) :
    ∃ g : adjointGroup .G2 K, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  classical
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card Nat.prime_two (by omega) hK
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have := Fintype.ofFinite (K ≃+* K)
  let φ : E → {σ : K ≃+* K // σ ^ p = 1} := fun e =>
    ⟨Θ e, by
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (A := E) (e : MulAut _) e.2, map_one]⟩
  have hcard : Nat.card {σ : K ≃+* K // σ ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  have hlt : Nat.card {σ : K ≃+* K // σ ^ p = 1} < Nat.card E := by
    rw [hEc]
    have := hp.two_le
    nlinarith
  have := Fintype.ofFinite E
  have hlt' : Fintype.card {σ : K ≃+* K // σ ^ p = 1} < Fintype.card E := by
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  obtain ⟨a, b, hab, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hlt'
  have hΘ : Θ ((a : MulAut _)⁻¹ * (b : MulAut _)) = 1 := by
    have h1 : Θ (a : MulAut _) = Θ (b : MulAut _) := congrArg Subtype.val hφ
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have hmem : (a : MulAut _)⁻¹ * (b : MulAut _) ∈ Θ.ker := hΘ
  rw [hker] at hmem
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_one] at hg
    apply hab
    have h1 : a.1 = b.1 := by
      have := congrArg (fun z => a.1 * z) hg
      simpa using this
    exact Subtype.ext h1
  · rw [hg]
    exact E.mul_mem (E.inv_mem a.2) b.2

omit [Finite K] in
theorem exists_conj_entrywise (hp : p.Prime) (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup .G2 K)) (hα : IsOuterOfOrder p α) :
    ∃ (h0 : adjointGroup .G2 K) (σ : K ≃+* K), orderOf σ = p ∧
      MulAut.conj h0 * α * (MulAut.conj h0)⁻¹ = entrywiseAdjointAut .G2 σ := by
  obtain ⟨hord, hout⟩ := hα
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
  have hαeq : α = MulAut.conj x * entrywiseAdjointAut .G2 σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  obtain ⟨hσord, -, ⟨h0, hh0⟩, -⟩ :=
    even_G2_noninner_prime_local_core_trivial hf hK hp ⊤ le_top ⟨α, Subgroup.mem_top _⟩
      (fun ⟨g, hg⟩ => hout g hg.symm) (by rw [Subgroup.orderOf_mk]; exact hord) x σ hαeq
  exact ⟨h0, σ, hσord, hh0⟩

end Descent

section Main


theorem fieldAutData_G2 (hpair : SubfieldPairG2) {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) :
    FieldAutData (adjointGroup .G2 K) p := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have : Fact p.Prime := ⟨hp⟩
  refine fieldAutData_of_standard (MulAut.conj : adjointGroup .G2 K →* MulAut _).range
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut .G2 σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_conj_mem_of_plane hp hf hK E hEc
  · intro α hα
    obtain ⟨h0, σ, hσ, h⟩ := exists_conj_entrywise hp hf hK α hα
    refine ⟨(MulAut.conj h0)⁻¹, ?_, entrywiseAdjointAut .G2 σ, ⟨σ, hσ, rfl⟩, ?_⟩
    · exact (MulAut.conj : adjointGroup .G2 K →* MulAut _).range.inv_mem ⟨h0, rfl⟩
    · rw [← h]
      group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    rw [fixedSubgroup_entrywise_eq, fixedSubgroup_entrywise_eq]
    exact g2Fixed_congr (fixedField_eq_of_orderOf Nat.prime_two (by omega) hK hσ hτ)
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    rw [fixedSubgroup_entrywise_eq] at hx hc
    exact eq_one_of_central_g2Fixed σ hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d ⟨g, rfl⟩ hne
    rw [fixedSubgroup_entrywise_eq] at hne ⊢
    exact hpair K ‹CharP K 2› σ p hp hp5 hσ g hne

end Main

section Index


theorem extSeitzAtOuter_G2_of_pair (hpair : SubfieldPairG2) {q : TauCeti.PrimePower}
    (hq2 : q.p = 2) : ExtSeitzAtOuter (.G2 q) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hc hout
  obtain ⟨X, hXf, hXfin, hX, ⟨e⟩⟩ := exists_adjointG2_model hiso
  rw [hq2] at hX
  have hf : 2 ≤ q.exponent := by
    obtain ⟨hv, -⟩ := hiso
    have h3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rw [TauCeti.PrimePower.card_def, hq2] at h3
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [h1] at h3
    norm_num at h3
  have hd : FieldAutData K p := (fieldAutData_G2 hpair hp hp5 hf hX).of_mulEquiv e hp
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

end Index

end CFSG.RankThree.PartOne.SEITZ2
