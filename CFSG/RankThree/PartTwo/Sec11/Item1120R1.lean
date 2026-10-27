module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V1
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarGeneric
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarL3
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarD4
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofBound
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofND
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
public import CFSG.RankThree.PartTwo.Sec4.Item48Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


theorem item1120_of_standing
    (h113 : Item113) (h117 : Item117) (h118 : Item118)
    (h119 : Item119) : Item1120 :=
  item1120_of_V0_kfacts Sec4.rank3II_4_5 h113 h117 h118 h119
    (step1120V0_of Sec4.rank3II_4_5 h113 h117 (Sec4.rank3II_4_8_of Sec4.rank3II_4_5)
      (Item1120V0Bar.step1120V0Bar_of_fam Sec4.rank3II_4_5 h113 h117 Item1120V0Bar.v0FamG2
          Item1120V0Bar.v0FamD4 Item1120V0Bar.v0FamL3))
    (kFact1117CubeG2_of_ss KS11Lie7Proof.normCentJ1117G2Ss_holds
      KS11Lie6Proof.normCentJ1117D4Ss_holds)
    KS11LieProof.kFact1117CubeL3

theorem item1120_of_standing_no118
    (h113 : Item113) (h117 : Item117) (h119 : Item119) :
    Item1120 :=
  item1120_of_standing h113 h117
    (item118_of h117 Sec4.rank3II_4_5 (Sec4.rank3II_4_8_of Sec4.rank3II_4_5)) h119

end Certified

end CFSG.RankThree.PartTwo.Sec11
