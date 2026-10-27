module

public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

@[expose] def Item223OneInnerConcl [Finite G] (A : Subgroup G) (φ : MulAut A) (Z : Subgroup G) :
    Prop :=
  ∃ m : ℕ, 1 < m ∧ Odd m ∧ Nonempty (Z ≃* projSU 4 2 m) ∧
    Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
    inSubgroup (aschbacherSolvableCore 3) Z = ⊥ ∧ (∀ x ∈ A, ¬ Sec4.InducesOuterTheta x Z) ∧
    Nat.card (A ⊓ Z : Subgroup G) = 3 ^ 3 ∧
    Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3

@[expose] def Item233ZReflDStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item231Concl A → ∀ φ ∈ dStar A, ∀ Z ∈ lStar A, kOf A φ ≤ Z →
      (Nat.card A = 3 ^ 4 → Item223OneInnerConcl A φ Z) →
      (Nat.card A = 3 ^ 3 → ∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z) →
        ∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A

@[expose] def Item233ZRootGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item231Concl A → ∀ φ ∈ dStar A, ∀ Z ∈ lStar A, kOf A φ ≤ Z →
      (Nat.card A = 3 ^ 4 → Item223OneInnerConcl A φ Z) →
      (Nat.card A = 3 ^ 3 → ∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z) →
      (∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A) →
        Z ≤ (Z ⊓ Subgroup.normalizer (A : Set G)) ⊔
          ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ

end CFSG.RankThree.PartTwo.Sec21
