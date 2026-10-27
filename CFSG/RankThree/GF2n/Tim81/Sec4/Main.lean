module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Thm410
public import CFSG.RankThree.GF2n.Tim81.Sec4.HA5

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

theorem sec41Statement_of_theoremA
    (hA : TheoremAStmt) (h79 : Tim79aStatementWCQ) :
    Sec41Statement :=
  sec41Statement_of_inputs hA h79 ha5Statement centralTIStatement

theorem sec45Statement_of_theoremA
    (hA : TheoremAStmt) (h79 : Tim79aStatementWCQ) :
    Sec45Statement :=
  sec45Statement_of_sec41 h79 (sec41Statement_of_theoremA hA h79)

end CFSG.RankThree.GF2n.Tim81
