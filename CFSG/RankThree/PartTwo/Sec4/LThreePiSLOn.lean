module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiOn

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts

variable {G : Type} [Group G] [Finite G]

@[expose] def InducesTypeOnSL (L : Subgroup G) (x : G) (k : ℕ) : Prop :=
  ∃ (hx : x ∈ Subgroup.normalizer (L : Set G)) (π : Bool) (p f : ℕ) (K : Type) (_ : Field K)
    (_ : PiField π p f K) (_ : ModThree π (p ^ f)) (e : L ≃* slPi π 3 (p ^ f) K)
    (y : GL (Fin 3) K), y ∈ glPi π 3 (p ^ f) K ∧ Type123 π (p ^ f) K y k ∧
      ∀ z : L, ((e (L.normalizerMonoidHom ⟨x, hx⟩ z) : GL (Fin 3) K)) =
        y * (e z : GL (Fin 3) K) * y⁻¹

@[expose] def IsTypeCOnSL (E L : Subgroup G) : Prop :=
  ∃ (hE : E ≤ Subgroup.normalizer (L : Set G)) (π : Bool) (p f : ℕ) (K : Type) (_ : Field K)
    (_ : PiField π p f K) (_ : ModThree π (p ^ f)) (e : L ≃* slPi π 3 (p ^ f) K)
    (D : Subgroup (GL (Fin 3) K)), IsTypeC π (p ^ f) K D ∧
      (∀ x : E, ∃ y ∈ D, ∀ z : L,
        ((e (L.normalizerMonoidHom ⟨x, hE x.2⟩ z) : GL (Fin 3) K)) =
          y * (e z : GL (Fin 3) K) * y⁻¹) ∧
      ∀ y ∈ D, ∃ x : E, ∀ z : L,
        ((e (L.normalizerMonoidHom ⟨x, hE x.2⟩ z) : GL (Fin 3) K)) =
          y * (e z : GL (Fin 3) K) * y⁻¹

@[expose] def Alt411 (L A : Subgroup G) (c : G) : Prop :=
  (Nat.card A = 27 ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ IsTypeCOnSL A L) ∨
  (Nat.card A = 27 ∧ IsHeisCentral ↥(A ⊔ L) ↥L) ∨
  (Nat.card A = 27 ∧ IsSLThreePiTwo ↥(A ⊔ L) ∧ ∃ a ∈ A, InducesTypeOnSL L a 3 ∧
    ∃ u v : G, u ∈ Subgroup.centralizer (L : Set G) ∧ u ∉ L ∧ v ∈ L ∧
      v ∉ Subgroup.centralizer (L : Set G) ∧ orderOf u = 3 ∧ orderOf v = 3 ∧
      A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) = Subgroup.closure {c, u * v} ∧
      A ⊔ L = L ⊔ Subgroup.closure {u, a} ∧ u * a * u⁻¹ * a⁻¹ = c) ∨
  (Nat.card A = 27 ∧ ∃ σ ∈ A, InducesStdKind L σ .field ∧
    A = Subgroup.zpowers σ ⊔ (A ⊓ L) ∧ Subgroup.zpowers σ ⊓ L = ⊥) ∨
  (Nat.card A = 81 ∧ ∃ σ ∈ A, InducesStdKind L σ .field ∧
    (∃ n : ℕ, Odd n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ n) ^ 2 ∧
      Nonempty (L ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K)) ∧
    Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) = 27 ∧
    ((Nat.card (A ⊓ L : Subgroup G) = 9 ∧
        IsTypeCOnSL (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G))) L) ∨
      IsHeisCentral ↥((A ⊓ (L ⊔ Subgroup.centralizer (L : Set G))) ⊔ L) ↥L)) ∨
  (Nat.card A = 27 ∧ ∃ σ ∈ A, InducesStdKind L σ .field ∧
    ∃ u v : G, u ∈ Subgroup.centralizer (L : Set G) ∧ u ∉ L ∧ v ∈ L ∧
      v ∉ Subgroup.centralizer (L : Set G) ∧ orderOf u = 3 ∧ orderOf v = 3 ∧
      A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) = Subgroup.closure {c, u * v} ∧
      u * σ * u⁻¹ * σ⁻¹ = c)

@[expose] def Alt412 (L A : Subgroup G) (c : G) : Prop :=
  (Nat.card A = 27 ∧ A ⊔ L = Subgroup.zpowers c ⊔ L ∧
    (∀ x ∈ A ⊓ L, x ≠ 1 → InducesTypeOn L x 1) ∧
    ∀ x ∈ A ⊓ L, x ≠ 1 → ∀ y ∈ A ⊓ L, y ≠ 1 →
      ∃ n ∈ L ⊓ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G), n * x * n⁻¹ = y) ∨
  (Nat.card A = 27 ∧ IsTypeCOn A L) ∨
  (Nat.card A = 27 ∧ (∃ a ∈ A, InducesTypeOn L a 3) ∧
    ∃ b : G, A ⊓ L = Subgroup.zpowers b ∧ orderOf b = 3 ∧ InducesTypeOn L b 1) ∨
  (Nat.card A = 81 ∧ ∃ σ ∈ A, InducesStdKind L σ .field ∧
    ∃ n : ℕ, 1 ≤ n ∧ IsoLThreePi ↥L 2 n ∧
      Nat.card (Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) = 27 ∧
      (((∀ x ∈ A ⊓ L, x ≠ 1 → InducesTypeOn L x 1) ∧
          ∀ x ∈ A ⊓ L, x ≠ 1 → ∀ y ∈ A ⊓ L, y ≠ 1 →
            ∃ n ∈ L ⊓ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G), n * x * n⁻¹ = y) ∨
        (IsTypeCOn (Subgroup.zpowers c ⊔ (A ⊓ L)) L ∧ 2 ^ n % 3 = 2)))

end CFSG.RankThree.PartTwo.Sec4
