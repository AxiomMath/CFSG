module

public import CFSG.RankThree.PartTwo.Sec16.Item168StepsProofPGL
import CFSG.RankThree.PartTwo.KFacts.KS14Models131
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo

public section

namespace CFSG.RankThree.PartTwo.Sec17.Ronan17NoPGL

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17

theorem prodLBarS17_of_item1514
    (h131 : Item131) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) : ProdLBarS17 :=
  prodLBarS17_of_wired h131 KFacts.KS14.sporadicModels131 slTwoCenter
    (noPGL131S17_of_item1514 h1514 hMeets)

end CFSG.RankThree.PartTwo.Sec17.Ronan17NoPGL
