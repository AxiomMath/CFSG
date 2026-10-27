module

public import CFSG.RankThree.GF2n.Tim79aLeafAssemblyTI
public import CFSG.RankThree.GF2n.Tim79aSUModelGen
public import CFSG.RankThree.GF2n.Tim79a34Pairing

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open scoped commutatorElement

section Certified


theorem tim79aStatementWCQ_of_frontier'' (h2 : OddTranspNoSqE1Dich)
    (hL2 : CFSG.RankThree.GF2n.Tim81.OddTranspRootL2) (hT : TransvectionStatement)
    (h34Two : Tim79a34TwoTildeNoCentreStatement)
    (h34Big : Tim79a34BigTildeStatement) : Tim79aStatementWCQ :=
  tim79aStatementWCQ_of_remaining_noCentre_of_ti h2 hL2 hT
      (classicalRootIrrStatement_of_su_statements suCoreStatement_holds suIrrStatement_holds)
      (classicalRootInnerStatement_of_suModel suModelInner_holds)
      (classicalRootS2Statement_of_suModel suModelS2_holds) classicalRootS1Statement_holds
      tim79a33TildeStatement_holds h34Two h34Big

theorem tim79aStatementWCQ_of_remaining_34 (h2 : OddTranspNoSqE1Dich)
    (hL2 : CFSG.RankThree.GF2n.Tim81.OddTranspRootL2) (hT : TransvectionStatement)
    (hSum : Sec34SummandStatement) (hTwo : Tim79a34TwoTildeEndStatement)
    (hTwist : Tim79a34TwoTwistedStatement) (hBig : Tim79a34BigTildeEndStatement) :
    Tim79aStatementWCQ :=
  tim79aStatementWCQ_of_frontier'' h2 hL2 hT
    (tim79a34TwoTildeNoCentreStatement_of_parts
      (sec34ModuleStatement_of_summand_holds hSum) hTwo hTwist)
    (tim79a34BigTildeStatement_of_parts (sec34ModuleStatement_of_summand_holds hSum) hBig)

end Certified

end CFSG.RankThree.GF2n.Tim79a
