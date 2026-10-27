module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofKb
public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofClaim
public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofHJ
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16

theorem sec17OThreeSolv_of_res14 (h166 : Item166S17) (hbot : Item145BotS17)
    (h168 : Item168S17) (h146 : Item146S14) (h172 : Item172S17) (h9 : CardInfNineS17)
    (h165 : Item165S17) (hQ0 : Claim17Q0) (hI : Claim174Inner) (hKbO : Step174KbO) :
    Sec17OThreeSolv :=
  sec17OThreeSolv_of_printM h166 hbot h168 h146 h172 h9 kFact174_holds
    (claim174_of_inner h165 h9 hQ0 h146 h166 hI) (step174KbM_of_O h166 h146 hKbO)

theorem step177Contra_of_res14
    (h171 : Item171S17) (hbal : Step143Balance)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h166 : Item166S17) (hbot : Item145BotS17)
    (h168 : Item168S17) (h146 : Item146S14) (h172 : Item172S17) (h9 : CardInfNineS17)
    (h165 : Item165S17) (hQ0 : Claim17Q0) (hI : Claim174Inner) (hKbO : Step174KbO) :
    Step177Contra :=
  step177Contra_of_items h171 hbal h9 (step177OThreeSolv_of_sec17
    (sec17OThreeSolv_of_res14 h166 hbot h168 h146 h172 h9 h165 hQ0 hI hKbO)) h134 h48

end CFSG.RankThree.PartTwo.Sec17
