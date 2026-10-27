module

public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)

@[expose] def Item233ZRootGenThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item231Concl A → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ Z ∈ lStar A, kOf A φ ≤ Z →
      (∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z) →
      (∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A) →
        Z ≤ (Z ⊓ Subgroup.normalizer (A : Set G)) ⊔
          ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ

end CFSG.RankThree.PartTwo.Sec21
