module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

structure FF79CentL5 (x b z : G) : Prop where
  exists_decomp : ∃ X J' : Subgroup G, X ≤ Cen x ∧ J' ≤ Cen x ∧ Odd (Nat.card X) ∧
    Nonempty (J' ≃* GL (Fin 5) (ZMod 2)) ∧ (∀ u ∈ X, ∀ v ∈ J', u * v = v * u) ∧
    (∀ g ∈ Cen x, ∃ i : ℤ, ∃ u ∈ X, ∃ v ∈ J', g = x ^ i * u * v) ∧
    b ∈ J' ∧ z ∈ J' ∧ 7 ∣ Nat.card ↥(J' ⊓ Cen b)

structure FF79CentA5L3 (x b w : G) : Prop where
  exists_decomp : ∃ X K L : Subgroup G, X ≤ Cen x ∧ K ≤ Cen x ∧ L ≤ Cen x ∧
    Odd (Nat.card X) ∧ Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
    Nonempty (L ≃* GL (Fin 3) (ZMod 2)) ∧
    (∀ u ∈ X, ∀ v ∈ K, u * v = v * u) ∧ (∀ u ∈ X, ∀ v ∈ L, u * v = v * u) ∧
    (∀ u ∈ K, ∀ v ∈ L, u * v = v * u) ∧
    (∀ g ∈ Cen x, ∃ i : ℤ, ∃ u ∈ X, ∃ k ∈ K, ∃ l ∈ L, g = x ^ i * u * k * l) ∧
    w ∈ K ∧ b ∈ L

structure FF79Sec4Str (b : G) (J : Subgroup G) (b₁ b₂ : G) : Prop where
  equivJ : Nonempty (J ≃* GL (Fin 5) (ZMod 2))
  cent₁ : FF79CentL5 b₁ b b₂
  cent₂ : FF79CentL5 b₂ b b₁
  centβ : FF79CentA5L3 (b₁ * b₂) b (b₁ ^ 2 * b₂)
  centγ : FF79CentA5L3 (b₁ ^ 2 * b₂) b (b₁ * b₂)

@[expose] def FF79_4_3Str : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ → FF79Sec4Str b J b₁ b₂

end CFSG.RankThree.PartTwo.Sec21.FF79
