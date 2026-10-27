module

public import CFSG.RankThree.PartTwo.Sec21.Item233Skeleton
public import CFSG.RankThree.PartTwo.Sec21.Item233ComponentsOf
public import CFSG.RankThree.PartTwo.Sec21.Item233InnerDiagonal
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionMain

public section

namespace CFSG.RankThree.PartTwo.Sec21

theorem item233Centralizers_of_tables (h231 : Item231) (h232 : Item232)
    (ha : TerminalOrderThree) (hi : Item233ComponentsOne) (h45 : Sec4.Item4_5) :
    Item233Centralizers :=
  item233Centralizers_of h231 h232 ha (item233Components_of hi h45 h232)
    InnerDiagonal.innerDiagonalSL34

theorem rank3II_23_3_of_tables (h231 : Item231) (h232 : Item232) (ha : TerminalOrderThree)
    (hi : Item233ComponentsOne) (h45 : Sec4.Item4_5) : Item233 :=
  rank3II_23_3_of h231 h232 KFacts.KS21.terminalFusion
    (item233Centralizers_of_tables h231 h232 ha hi h45)

end CFSG.RankThree.PartTwo.Sec21
