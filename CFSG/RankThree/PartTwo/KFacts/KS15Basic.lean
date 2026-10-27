module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

@[expose] def KS15Z3PGLNonabelian : Prop :=
  ∀ (X : Type) [Group X] (p f : ℕ), IsZ3PGLThreeAt X p f → ∃ a b : X, a * b ≠ b * a

end CFSG.RankThree.PartTwo.KFacts
