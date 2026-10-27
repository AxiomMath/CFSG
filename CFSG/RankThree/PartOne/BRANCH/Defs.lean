module

public import CFSG.RankThree.PartOne.N143.Weyl613Small
public import CFSG.RankThree.PartOne.N143.Statements

public section

namespace CFSG.RankThree.PartOne.BRANCH

open CFSG.RankThree.PartOne.N143

@[expose] def EvenLieSevenRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    EvenLieTypeSmall X → ∀ q : ℕ, (q = 3 ∨ q = 5) → ∀ D : Subgroup X,
      CFSG.IsElementaryAbelian q D → Nat.card D = q ^ 7 → False

end CFSG.RankThree.PartOne.BRANCH
