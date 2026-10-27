module

public import CFSG.RankThree.GF2n.Tim79aCase1

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

section Certified

theorem tim79aStatementWCQ_of_two_statements (h1 : Tim75aTINotWCRoot) (h2 : OddTranspNoSqE1Dich)
    (hSq : Tim79aSquareStatement) (hTr : Tim79aTransvectionStatement) :
    Tim79aStatementWCQ :=
  tim79aStatementWCQ_of_inputs h1 h2 tim79aCase1Statement_holds hSq hTr

end Certified

end CFSG.RankThree.GF2n.Tim79a
