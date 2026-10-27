module

public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def Item228OneList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 → (∀ ρ ∈ wStar A, ¬ IsTransvectionOn ρ) →
      ∀ φ ∈ dStar A, ∀ X ∈ lStar A, kOf A φ ≤ X → ∀ m : ℕ, 0 < m → Even m →
        Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) →
          (Nonempty (X ≃* SL3 m) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 m)) ∨
              Nonempty (X ≃* projSU 4 2 m) ∨
              (m % 4 = 0 ∧ Nonempty (X ≃* projSU 4 2 (m / 2))) ∨
              ((m = 2 ∨ m = 4) ∧ Nonempty (X ≃* projSU 5 2 2))) ∨
            (m = 2 ∧ StatedClassicalModel X .PSp 2 5 1)

@[expose] def Item228NotPSp45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ X ∈ lStar A, kOf A φ ≤ X → ¬ StatedClassicalModel X .PSp 2 5 1

@[expose] def Item228Inspection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ ≠ φ → ∀ X ∈ lStar A, kOf A φ ≤ X → kOf A ψ ≤ X →
        Item228OneConcl A φ X → Item228OneConcl A ψ X →
        (ψ * φ = φ * ψ →
          ⁅kOf A φ, kOf A ψ⁆ = ⊥ ∨
          (kOf A φ ⊔ kOf A ψ ∈ lStar A ∧ ∃ m : ℕ, 0 < m ∧ m % 4 = 0 ∧
            Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
            Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 m)) ∧
            Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 (m / 2)) ∧
            ∃ w ∈ wStar A, w * φ * w⁻¹ = ψ) ∨
          (Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 4)) ∧
            Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 4)) ∧
            Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 2) ∧
            (∃ X' ∈ lStar A, kOf A φ ⊔ kOf A ψ ≤ X' ∧ Nonempty (X' ≃* projSU 5 2 2)) ∧
            ∃ w ∈ wStar A, w * φ * w⁻¹ = ψ)) ∧
        (ψ * φ ≠ φ * ψ →
          (kOf A φ ⊔ kOf A ψ ∈ lStar A ∧ Case222 A (kOf A φ ⊔ kOf A ψ) (kOf A φ) ∧
            IsEmpty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 5 2 2)) ∨
          (Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 2) ∧
            ∃ X' ∈ lStar A, kOf A φ ⊔ kOf A ψ ≤ X' ∧ Nonempty (X' ≃* projSU 5 2 2)))

end CFSG.RankThree.PartTwo.Sec21
