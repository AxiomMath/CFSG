module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def EvenSimpleList : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (e : ℕ), 1 ≤ e →
    (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; Sec4.IsoLThreePi X 2 e) →
    ∀ K : Subgroup X, IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      (∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      StatedClassicalModel K .PSL 2 3 2 ∨
      (∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧
        (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; IsLThreeEpsAt K 2 f))

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
