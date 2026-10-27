module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRemaining
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RAll
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmegaNSHolds
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93AC5

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.RankThree.GF2n.Stroth80

theorem gf2nType_of_tim79a_1111
    (h79 : Tim79aStatementWCQ) (h1111 : Stroth1111Statement) :
    GF2nTypeStatement :=
  gf2nType_of_remaining_three h79
    (stroth98Statement_of_leaves
        ⟨step93OmegaCaseBNSStatement_holds,
            (step93L2AltXHStatement_of_inputs stroth34Statement_unconditional stroth311aStatement_unconditional stroth311bCommStatement_unconditional stroth312bStatement_unconditional theoremXStatement_holds),
            CGT.Timmesfeld75.corollaryBStmt_of_theoremAStmt CGT.Timmesfeld75.theoremAStmt_holds,
            strothNoA2Spread_of_h1111 h1111⟩)
    h1111

end CFSG.RankThree.GF2n.Tim81
