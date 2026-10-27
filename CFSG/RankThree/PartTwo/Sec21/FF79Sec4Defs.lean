module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

@[expose] def FF79_4_4X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ → ∀ t : G, orderOf t = 2 → t * b₁ = b₁ * t → t * b₂ = b₂ * t →
      t * b * t⁻¹ = b⁻¹ → IsExtraspecialPGroup 2 ↥(Op 2 (Cen t))

variable {G : Type} [Group G]

structure FF79Inv (b b₁ b₂ t : G) : Prop where
  ord : orderOf t = 2
  comm₁ : t * b₁ = b₁ * t
  comm₂ : t * b₂ = b₂ * t
  inv : t * b * t⁻¹ = b⁻¹

@[expose] def FF79_JL5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J : Subgroup G), FF79Hyp 5 b J → IsLnq 5 2 1 J

@[expose] def FF79_4_4J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ → ∀ t : G, FF79Inv b b₁ b₂ t → J ≤ Cen t

@[expose] def FF79_4_4Beta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ → ∀ t : G, FF79Inv b b₁ b₂ t →
    ∀ x : G, (x = b₁ * b₂ ∨ x = b₁ ^ 2 * b₂) → ∀ y ∈ Op 2 (Cen t) ⊓ Cen x,
      y * b₁ = b₁ * y ∧ y * b₂ = b₂ * y ∧ y ^ 2 ∈ Subgroup.zpowers t

@[expose] def FF79_4_4Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ → ∀ t : G, FF79Inv b b₁ b₂ t →
    ∀ y ∈ Op 2 (Cen t) ⊓ Cen (b₁ * b₂), (∀ z ∈ Op 2 (Cen t), y * z = z * y) →
      y ∈ Subgroup.zpowers t

@[expose] def FF79_4_4Bi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ → ∀ t : G, FF79Inv b b₁ b₂ t →
    ∀ x : G, (x = b₁ ∨ x = b₂) → ∀ y ∈ Op 2 (Cen t) ⊓ Cen x, ∀ z ∈ Op 2 (Cen t) ⊓ Cen x,
      y * z * y⁻¹ * z⁻¹ ∈ Subgroup.zpowers t

end CFSG.RankThree.PartTwo.Sec21.FF79
