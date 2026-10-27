module

public import CFSG.RankThree.GF2n.Tim79aLeafAssembly
public import CFSG.RankThree.GF2n.Tim79aTINotWC

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.Transvection

section Certified

theorem tim79aStatementWCQ_of_remaining_noCentre_of_ti (h2 : OddTranspNoSqE1Dich)
    (hL2 : CFSG.RankThree.GF2n.Tim81.OddTranspRootL2) (hT : TransvectionStatement)
    (hIrr : ClassicalRootIrrStatement) (hIn : ClassicalRootInnerStatement)
    (hS2 : ClassicalRootS2Statement) (hS1 : ClassicalRootS1Statement)
    (h33 : Tim79a33TildeStatement) (h34Two : Tim79a34TwoTildeNoCentreStatement)
    (h34Big : Tim79a34BigTildeStatement) : Tim79aStatementWCQ :=
  tim79aStatementWCQ_of_remaining_noCentre tim75aTINotWCRoot_holds h2 hL2 hT hIrr hIn hS2 hS1 h33
    h34Two h34Big

end Certified

end CFSG.RankThree.GF2n.Tim79a
