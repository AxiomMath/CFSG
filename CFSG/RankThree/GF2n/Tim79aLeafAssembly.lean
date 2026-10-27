module

public import CFSG.RankThree.GF2n.Tim79aTransvectionTorus
public import CFSG.RankThree.GF2n.Tim79aTransvectionGeneration
public import CFSG.RankThree.GF2n.Tim79aBenderRootPairs
public import CFSG.RankThree.GF2n.Tim79aSec24Tilde
public import CFSG.RankThree.GF2n.Tim79aSec24CoreQuotient
public import CFSG.RankThree.GF2n.Tim79aSec24Irr
public import CFSG.RankThree.GF2n.Tim79aSec24Inner
public import CFSG.RankThree.GF2n.Tim79aSec25S1
public import CFSG.RankThree.GF2n.Tim79a32Tilde
public import CFSG.RankThree.GF2n.Tim79aWCQLeaves

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.Transvection

section Certified

theorem tim79aStatementWCQ_of_remaining_noCentre (h1 : Tim75aTINotWCRoot)
    (h2 : OddTranspNoSqE1Dich) (hL2 : CFSG.RankThree.GF2n.Tim81.OddTranspRootL2)
    (hT : TransvectionStatement) (hIrr : ClassicalRootIrrStatement)
    (hIn : ClassicalRootInnerStatement) (hS2 : ClassicalRootS2Statement)
    (hS1 : ClassicalRootS1Statement) (h33 : Tim79a33TildeStatement)
    (h34Two : Tim79a34TwoTildeNoCentreStatement) (h34Big : Tim79a34BigTildeStatement) :
    Tim79aStatementWCQ := by
  have hk : RootPairOfKindStatement := rootPairOfKindStatement_holds
  have h24 : Tim79aSec24TildeStatement := tim79aSec24TildeStatement_of_parts
    (tim79aSec24IrrTildeStatement_of_model hk (rootIrrAll_of_classical hIrr))
    (tim79aSec24InnerTildeStatement_of_model hk (rootInnerAll_of_classical hIn))
  have h25 : Tim79aSec25BarTildeStatement := tim79aSec25BarTildeStatement_of_parts
    (tim79aSec25S1TildeStatement_of_model hk (rootS1All_of_classical hS1))
    (tim79aSec25S2TildeStatement_of_model hk (rootS2All_of_classical hS2))
  have h34 : Tim79a34TildeStatement :=
    tim79a34TildeStatement_of_parts (tim79a34TwoTildeStatement_of_noCentre h34Two) h34Big
  exact tim79aStatementWCQ_of_two_statements h1 h2
    (tim79aSquareStatement_of_tilde_parts tim79aIdentBenderStatement_of_certs
      (tim79aIdentConnectedStatement_of_inputs hL2 hT transvectionGenerationStatement_holds
          transvectionTorusStatement_holds) h24 h25 tim79a32TildeStatement_holds h33 h34)
    (tim79aTransvectionStatement_of_tilde_parts_noCentre h24 h25 h33 h34Two)

end Certified

end CFSG.RankThree.GF2n.Tim79a
