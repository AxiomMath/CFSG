module

public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofL
public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofThree

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17

theorem item165S17_of_kfacts (hst : StellmacherKP)
    (hbot : Sec14.Item145BotS17) (h146 : Sec14.Item146S14) (h149 : Item149S14)
    (h153 : Item153MainR) (hQ : Step171CommQ) (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (h138 : Item138N) (hKU : KS165U) (hKL : KS165L) (hRes : Res165R) (hRed : Red165R) :
    Item165S17 :=
  item165S17_of hst hbot h146 h149 (step165E_of_kfacts h153 hQ h1514 hMeets h138 hKU hKL)
    (step165Three_of hRes hRed)

end CFSG.RankThree.PartTwo.Sec16
