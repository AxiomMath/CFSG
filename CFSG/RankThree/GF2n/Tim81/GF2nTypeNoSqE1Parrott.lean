module

public import CFSG.RankThree.GF2n.Tim81.GF2nTypeTim79a1111
public import CFSG.RankThree.GF2n.Tim79aFrontier47
public import CFSG.RankThree.GF2n.Stroth80.Sec1111Siegel

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.RankThree.GF2n.Stroth80

theorem gf2nType_of_noSqE1_parrott (h2 : Tim79a.OddTranspNoSqE1Dich)
    (hParrott : Tim79a.ParrottFi22Statement) : GF2nTypeStatement :=
  gf2nType_of_tim79a_1111 (Tim79a.tim79aStatementWCQ_of_noSqE1_parrott h2 hParrott)
    stroth1111Statement_holds

end CFSG.RankThree.GF2n.Tim81
