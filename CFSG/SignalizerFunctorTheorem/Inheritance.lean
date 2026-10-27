module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic
public import CFSG.SignalizerFunctorTheorem.Inheritance.HypB
public import CFSG.SignalizerFunctorTheorem.Inheritance.Normalizer

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

variable {G : Type*} [Group G]

theorem mcBrideHypothesisB_of_centralizers [Finite G] {p : ℕ} (hp : p.Prime)
    {A W : Subgroup G} (hA : IsElemAbelian p A) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hcop : Nat.Coprime p (Nat.card W))
    (hcent : ∀ a ∈ A, a ≠ 1 →
      signalizerMcBrideHypothesisB p (W ⊓ Subgroup.centralizer {a}))
    (hfaith : ∀ K L : Subgroup G, K ≤ W → L ≤ K → ∀ [(L.subgroupOf K).Normal],
      A ≤ Subgroup.normalizer (K : Set G) → A ≤ Subgroup.normalizer (L : Set G) →
      IsSimpleGroup (K ⧸ L.subgroupOf K) → (∃ x y : K ⧸ L.subgroupOf K, x * y ≠ y * x) →
      ∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ K, x⁻¹ * (a * x * a⁻¹) ∈ L) :
    signalizerMcBrideHypothesisB p W := by
  refine ⟨hp, hcop, ?_⟩
  intro K L hKW hLK _ hsimple hnc
  have := hsimple
  have hXK : IsSectionOf (K ⧸ L.subgroupOf K) K :=
    IsSectionOf.of_surjective (QuotientGroup.mk' (L.subgroupOf K))
      (QuotientGroup.mk'_surjective _)
  have hKW' : IsSectionOf K W :=
    (IsSectionOf.refl K).of_injective (Subgroup.inclusion hKW) (Subgroup.inclusion_injective hKW)
  have hXW : IsSectionOf (K ⧸ L.subgroupOf K) W := hXK.trans hKW'
  obtain ⟨a, ha, ha1, hsec⟩ := exists_centralizer_section_of_normalizer hp hnc hAW
    (fun a ha => hA.2 a ha) hcop hfaith hXW
  exact signalizerMcBrideHypothesisA_of_isSectionOf (hcent a ha ha1) hsec hnc

end CFSG.SignalizerFunctorTheorem
