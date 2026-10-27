module

public import CFSG.RankThree.PartOne.TCX.LayerEngine
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.TCX.F4

section ZPowers

variable {G : Type} [Group G]

@[expose] def stabSubgroup (Q : Subgroup G) : Subgroup (MulAut G) where
  carrier := {γ | (∀ g ∈ Q, γ g ∈ Q) ∧ ∀ g ∈ Q, γ⁻¹ g ∈ Q}
  mul_mem' := fun {a b} ha hb => ⟨fun g hg => ha.1 _ (hb.1 g hg), fun g hg => by
    rw [mul_inv_rev]
    exact hb.2 _ (ha.2 g hg)⟩
  one_mem' := ⟨fun g hg => hg, fun g hg => hg⟩
  inv_mem' := fun {a} ha => ⟨ha.2, fun g hg => by rw [inv_inv]; exact ha.1 g hg⟩

@[expose] def innerOnSubgroup (Q : Subgroup G) : Subgroup (MulAut G) where
  carrier := {γ | γ ∈ stabSubgroup Q ∧ ∃ e ∈ Q, ∀ g ∈ Q, γ g = e * g * e⁻¹}
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨ha1, e₁, he₁, hae₁⟩ := ha
    obtain ⟨hb1, e₂, he₂, hbe₂⟩ := hb
    refine ⟨mul_mem ha1 hb1, e₁ * e₂, mul_mem he₁ he₂, fun g hg => ?_⟩
    have hg2 : e₂ * g * e₂⁻¹ ∈ Q := mul_mem (mul_mem he₂ hg) (inv_mem he₂)
    rw [MulAut.mul_apply, hbe₂ g hg, hae₁ _ hg2]
    group
  one_mem' := ⟨one_mem _, 1, one_mem _, fun g _ => by simp⟩
  inv_mem' := fun {a} ha => by
    obtain ⟨ha1, e, he, hae⟩ := ha
    refine ⟨inv_mem ha1, e⁻¹, inv_mem he, fun g hg => ?_⟩
    have hmem : a⁻¹ g ∈ Q := ha1.2 g hg
    have h1 : a (a⁻¹ g) = g := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    have h2 := hae _ hmem
    rw [h1] at h2
    have h3 : e⁻¹ * g * e = a⁻¹ g := by
      conv_lhs => rw [h2]
      group
    rw [inv_inv, ← h3]

theorem mem_stabSubgroup_of_pow_eq_one {p : ℕ} (hp : 0 < p) {β : MulAut G} (hβp : β ^ p = 1)
    {Q : Subgroup G} (hQβ : ∀ g ∈ Q, β g ∈ Q) : β ∈ stabSubgroup Q := by
  refine ⟨hQβ, fun g hg => ?_⟩
  have hit : ∀ (k : ℕ) (g : G), g ∈ Q → (β ^ k) g ∈ Q := by
    intro k
    induction k with
    | zero => intro g hg; simpa using hg
    | succ k ih =>
      intro g hg
      rw [pow_succ', MulAut.mul_apply]
      exact hQβ _ (ih g hg)
  have hinv : β⁻¹ = β ^ (p - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hp, hβp]
  rw [hinv]
  exact hit _ g hg

theorem mem_stabSubgroup_of_zpowers_eq {p : ℕ} (hp : 0 < p) {α β : MulAut G}
    (hzp : Subgroup.zpowers α = Subgroup.zpowers β) (hβp : β ^ p = 1) {Q : Subgroup G}
    (hQβ : ∀ g ∈ Q, β g ∈ Q) : α ∈ stabSubgroup Q := by
  have hβ := mem_stabSubgroup_of_pow_eq_one hp hβp hQβ
  have : α ∈ Subgroup.zpowers β := hzp ▸ Subgroup.mem_zpowers α
  exact (Subgroup.zpowers_le.2 hβ) this

theorem fixed_of_zpowers_eq {α β : MulAut G} (hzp : Subgroup.zpowers α = Subgroup.zpowers β)
    {g : G} (h : β g = g) : α g = g := by
  have hβ : β ∈ MulAction.stabilizer (MulAut G) g := by
    rw [MulAction.mem_stabilizer_iff]
    exact h
  have : α ∈ Subgroup.zpowers β := hzp ▸ Subgroup.mem_zpowers α
  have := (Subgroup.zpowers_le.2 hβ) this
  rw [MulAction.mem_stabilizer_iff] at this
  exact this

theorem layerClaims_of_zpowers_eq {p : ℕ} (hp : 0 < p) {α β : MulAut G}
    (hzp : Subgroup.zpowers α = Subgroup.zpowers β) (hβp : β ^ p = 1) {Q : Subgroup G}
    (hQβ : ∀ g ∈ Q, β g ∈ Q) (h : LayerClaimsF4 p β Q) : LayerClaimsF4 p α Q := by
  obtain ⟨hnon, hmodel, t₁, ht₁, hβ₁, t₂, ht₂, hβ₂, ho₁, ho₂, hnc⟩ := h
  have hαS : α ∈ stabSubgroup Q := mem_stabSubgroup_of_zpowers_eq hp hzp hβp hQβ
  have hzp' : Subgroup.zpowers β = Subgroup.zpowers α := hzp.symm
  refine ⟨fun e he hα => ?_, hmodel, t₁, ht₁, fixed_of_zpowers_eq hzp hβ₁, t₂, ht₂,
    fixed_of_zpowers_eq hzp hβ₂, ho₁, ho₂, hnc⟩
  have hαI : α ∈ innerOnSubgroup Q := ⟨hαS, e, he, hα⟩
  have hβα : β ∈ Subgroup.zpowers α := hzp' ▸ Subgroup.mem_zpowers β
  obtain ⟨-, e', he', hβe'⟩ := (Subgroup.zpowers_le.2 hαI) hβα
  exact hnon e' he' hβe'

theorem singleLayerData_of_zpowers_eq {p : ℕ} (hp : 0 < p) {α β : MulAut G}
    (hzp : Subgroup.zpowers α = Subgroup.zpowers β) (hβp : β ^ p = 1) {X : Subgroup G}
    (h : SingleLayerData p β X) : SingleLayerData p α X := by
  obtain ⟨D, hD, hst, huniq, hfix, hclaims⟩ := h
  have hαS : α ∈ stabSubgroup D := mem_stabSubgroup_of_zpowers_eq hp hzp hβp hst
  refine ⟨D, hD, hαS.1, huniq, fun g hg hαg h2 => hfix g hg (fixed_of_zpowers_eq hzp.symm hαg) h2,
    layerClaims_of_zpowers_eq hp hzp hβp hst hclaims⟩

end ZPowers

section Entrywise

variable {τ : Tag} {K : Type} [Field K]

theorem zpowers_entrywiseAdjointAut_eq {σ σ₀ : K ≃+* K}
    (h : Subgroup.zpowers σ = Subgroup.zpowers σ₀) :
    Subgroup.zpowers (entrywiseAdjointAut τ σ) = Subgroup.zpowers (entrywiseAdjointAut τ σ₀) := by
  have h1 := MonoidHom.map_zpowers (entrywiseAdjointAutHom (τ := τ) (K := K)) σ
  have h2 := MonoidHom.map_zpowers (entrywiseAdjointAutHom (τ := τ) (K := K)) σ₀
  rw [h, h2] at h1
  exact h1.symm

end Entrywise

end CFSG.RankThree.PartOne.TCX
