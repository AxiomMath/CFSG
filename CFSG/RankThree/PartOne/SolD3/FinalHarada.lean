module

public import CFSG.RankThree.PartOne.SolD3.Final
public import CFSG.LocalAnalysis.OddStandard.Harada75

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.CGT.PushingUpLit.SolK

theorem solDegreeThreeRNe1_of_harada
    (hE2 : SolomonTimmesfeldTight) (hOrd : TightSmallGroupOrders)
    (hWC3 : WCBlockCentralizerThree) : SolDegreeThreeRNe1 :=
  solDegreeThreeRNe1_of hE2 hOrd CFSG.OddStandard.Harada75.haradaInput_holds hWC3

end CFSG.RankThree.PartOne.SolD3
