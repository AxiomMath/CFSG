module

public import CFSG.RankThree.PartTwo.Sec11.RFacts
public import CFSG.RankThree.PartTwo.KFacts.K71bOutAbelian

public section

namespace CFSG.RankThree.PartTwo.Sec11

theorem outAbelian1016 : OutAbelian1016 := fun _ _ _ hX σ τ =>
  KFacts.isInnerAut_commutator_of_isList1016_all hX σ τ

end CFSG.RankThree.PartTwo.Sec11
