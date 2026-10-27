module

public import CFSG.RankThree.PartTwo.Sec11.Item11CloseChain
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE

public section

namespace CFSG.RankThree.PartTwo

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem item4_22_holds
    : Sec4.Item4_22 :=
  CFSG.RankThree.PartTwo.KFacts.rank3II_4_22_of_items_narrow41
    CFSG.RankThree.PartTwo.Sec4.rank3II_4_5
    CFSG.RankThree.PartTwo.Sec4.diag_item41LargePrime_holds
    CFSG.RankThree.PartTwo.Sec11.Close.closed_sec4Item4_1ThreeCover
    CFSG.RankThree.PartTwo.Sec4.diag_item43_holds

end CFSG.RankThree.PartTwo
