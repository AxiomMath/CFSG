module

public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus localRank)

@[expose] def Item228LThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, φ ≠ ψ → ∀ X ∈ lStar A, kOf A φ ⊔ kOf A ψ ≤ X →
        ((∃ k : ℕ, Nonempty (X ≃* projSU 4 2 k)) ∨ Nonempty (X ≃* projSU 5 2 2)) →
        X ∈ lThreeStar A

@[expose] def Item229UnitaryRoots : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, orderOf (φ * ψ) = 4 → ∀ b : ℕ, 0 < b →
        Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 b) →
        (Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 b)) ∧
            Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 (2 * b)))) ∨
          (Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 (2 * b))) ∧
            Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 b)))

@[expose] def CentralExtensionTrivial229 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    ∀ m : ℕ, 0 < m → Even m →
      (Nonempty (X ⧸ Subgroup.center X ≃* projSL 4 (GaloisField 2 m)) ∨
        Nonempty (X ⧸ Subgroup.center X ≃* projSp 3 (GaloisField 2 m)) ∨
        (∃ b c : GaloisField 2 m, (∀ s : GaloisField 2 m, s ^ 2 + b * s + c ≠ 0) ∧
          Nonempty (X ⧸ Subgroup.center X ≃* projOmegaMinus 3 (GaloisField 2 m) b c)) ∨
        Nonempty (X ⧸ Subgroup.center X ≃* projSU 6 2 m)) →
      Subgroup.center X = ⊥

@[expose] def LocalRankLowerBound229 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m : ℕ), Even m →
    ((4 ≤ m ∧ (Nonempty (X ≃* projSL 4 (GaloisField 2 m)) ∨
        Nonempty (X ≃* projSp 3 (GaloisField 2 m)))) ∨
      (2 ≤ m ∧ ((∃ b c : GaloisField 2 m, (∀ s : GaloisField 2 m, s ^ 2 + b * s + c ≠ 0) ∧
          Nonempty (X ≃* projOmegaMinus 3 (GaloisField 2 m) b c)) ∨
        Nonempty (X ≃* projSU 6 2 m)))) →
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ 3 ≤ localRank p X

end CFSG.RankThree.PartTwo.Sec21
