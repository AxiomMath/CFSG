module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426Rest

@[expose] def ONThreeCentralizer : Prop :=
  ∀ x : Blueprint.NativeSporadic.ON, orderOf x = 3 →
    Nat.card (Subgroup.centralizer {x}) = 3240

end CFSG.RankThree.PartTwo.KFacts.K426Rest
