module

public import CFSG.RankThree.PartTwo.Sec21.Item211

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def KS222Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L ℓ : Subgroup G) (n : ℕ), 0 < n → Even n →
    Nonempty (L ≃* projSp 2 (GaloisField 2 n)) → ℓ ≤ L → Nat.card ℓ = 3 →
      Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (ℓ : Set G)) ≃*
        projSL 2 (GaloisField 2 n))

@[expose] def KS222U4Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L ℓ : Subgroup G) (n : ℕ), 0 < n → Even n →
    Nonempty (L ≃* projSU 4 2 n) → ℓ ≤ L → Nat.card ℓ = 3 →
      Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (ℓ : Set G)) ≃*
          projSL 2 (GaloisField 2 n)) ∨
        Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (ℓ : Set G)) ≃*
          projSL 2 (GaloisField 2 (2 * n)))

@[expose] def KS222U5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L ℓ : Subgroup G), Nonempty (L ≃* projSU 5 2 2) →
    ℓ ≤ L → Nat.card ℓ = 3 →
      Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (ℓ : Set G)) ≃*
          projSL 2 (GaloisField 2 4)) ∨
        StatedClassicalModel
          (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (ℓ : Set G))) .PSU 3 2 2

@[expose] def KS222SL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A : Subgroup G) (n : ℕ), 0 < n → Even n →
    Nonempty (L ≃* SL3 n) → CFSG.Assembly.IsElemAbelian 3 A →
    A ≤ Subgroup.normalizer (L : Set G) → IsTypeCOnBarSL A L →
    ∀ b ∈ A, (∃ x ∈ L, x * b ≠ b * x) →
      Even (Nat.card (L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G)) →
      Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≃*
        projSL 2 (GaloisField 2 n))

@[expose] def KS222U4Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A : Subgroup G) (c : G) (n : ℕ), 1 < n → Odd n →
    Nonempty (L ≃* projSU 4 2 n) → CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 3 ^ 4 →
    c ∈ A → c ∉ L → L ≤ Subgroup.centralizer ({c} : Set G) →
    Nat.card (A ⊓ L : Subgroup G) = 3 ^ 3 →
      starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ {φ | IsReflectionOn φ}) ∧
        ∀ φ ∈ starOf A L, IsReflectionOn φ →
          Nonempty (inSubgroup perfectResidual
              (L ⊓ Subgroup.centralizer (fixedInG A φ : Set G)) ≃*
            projSL 2 (GaloisField 2 n))

end CFSG.RankThree.PartTwo.Sec21
