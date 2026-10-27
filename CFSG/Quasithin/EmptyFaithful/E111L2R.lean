module

public import CFSG.Quasithin.EmptyFaithful.E111RComp

public section

namespace CFSG.Quasithin.E2.E22N.E111L

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R

@[expose] def KleinMemberInner (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T A S : Subgroup G), E111Reduced G X T →
    (∀ S' : Subgroup G, IsComp X S' → IsPSL 2 p 1 ↥S') → A ≤ T → IsElemAbelian 2 A →
    IsComp X S →
    4 ≤ (A ⊓ Subgroup.centralizer (S : Set G)).relIndex (A ⊓ Subgroup.normalizer (S : Set G)) →
    (∀ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
      s⁻¹ * a ∈ Subgroup.centralizer (S : Set G)) →
    ∀ z ∈ T ⊓ S, orderOf z = 2 → (∀ x ∈ T ⊓ S, z * x = x * z) →
    ∃ K : Subgroup G, E1.IsE 1 ⊤ T A K ∧
      ∃ g ∈ K, g ∈ Subgroup.normalizer (S : Set G) ∧ g * z ≠ z * g

@[expose] def KleinMemberOuter (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T A S : Subgroup G), E111Reduced G X T →
    (∀ S' : Subgroup G, IsComp X S' → IsPSL 2 p 1 ↥S') → A ≤ T → IsElemAbelian 2 A →
    IsComp X S →
    4 ≤ (A ⊓ Subgroup.centralizer (S : Set G)).relIndex (A ⊓ Subgroup.normalizer (S : Set G)) →
    (∃ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∀ s ∈ S,
      s⁻¹ * a ∉ Subgroup.centralizer (S : Set G)) →
    ∀ z ∈ T ⊓ S, orderOf z = 2 → (∀ x ∈ T ⊓ S, z * x = x * z) →
    ∃ K : Subgroup G, E1.IsE 1 ⊤ T A K ∧
      ∃ g ∈ K, g ∈ Subgroup.normalizer (S : Set G) ∧ g * z ≠ z * g

end CFSG.Quasithin.E2.E22N.E111L
