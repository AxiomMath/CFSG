module

public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def EvenRankTwoExceptionalNoPCube : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ),
    (ChevalleyExceptionalModel X .trialityD4 2 f ∨ ReeTitsModel X .twistedF4 2 f) →
    ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ E : Subgroup X, IsElementaryAbelian p E → Nat.card E ≠ p ^ 3

end CFSG.RankThree.PartOne.N143X
