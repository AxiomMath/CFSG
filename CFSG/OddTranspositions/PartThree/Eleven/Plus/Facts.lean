module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Quandle
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Factors
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Frame

public section

namespace CFSG.OddTranspositions.PartThree


theorem o4PlusFacts_plusPerm : O4PlusFacts plusPerm plusClass :=
  ⟨card_plusPerm, plusClass_noncomm, plusClass_primitive, index_commutator_plusPerm,
    exists_plusFactors, exists_plusFrame, plusClass_perp⟩

end CFSG.OddTranspositions.PartThree
