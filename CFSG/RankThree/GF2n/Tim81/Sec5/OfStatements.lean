module

public import CFSG.RankThree.GF2n.Tim81.RootHypConj

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

theorem Sec5Hyp.of_statements (h79 : Tim79aStatementWCQ) (h45 : Sec45Statement)
    (h : RootHyp M V) : Sec5Hyp M V where
  root a := RootHyp.conjSubgroup h a
  sec45 a := h45 G (conjSubgroup a M) (conjSubgroup a V) (RootHyp.conjSubgroup h a)
  le_pCore a L hL :=
    RootHyp.le_pCore_of_isHMember h79 (RootHyp.conjSubgroup h a) hL

end CFSG.RankThree.GF2n.Tim81
