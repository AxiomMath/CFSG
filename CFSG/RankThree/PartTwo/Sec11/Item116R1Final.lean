module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1Assembly
public import CFSG.RankThree.PartTwo.Sec11.Item116R1StarTwo
public import CFSG.RankThree.PartTwo.KFacts.KS116LinProof

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

theorem residueTR1_of_core
    (hB : KFacts.BlackburnRankTwo) (hLin : KFacts.NoDoubleComponentGL)
    (hFC : FactFieldCentralizerL2Odd) (hFC3 : FactFieldCentralizerL3)
    (h45 : Sec4.Item4_5) (h113 : Item113) (hcore : Item116P2bCore) (hP2c : Item116P2c)
    (hCD : ResidueR1TwoStarCD) (hC38 : ResidueR1TwoStarCL38)
    (hCodd : ResidueR1TwoStarCOdd) : ResidueTR1 :=
  residueTR1_of_remaining hB hLin hFC hFC3 h45 h113 hcore hP2c fiveCaseCore hCD hC38 hCodd

theorem residueTR1_of_core'
    (hB : KFacts.BlackburnRankTwo)
    (hFC : FactFieldCentralizerL2Odd) (hFC3 : FactFieldCentralizerL3)
    (h45 : Sec4.Item4_5) (h113 : Item113) (hcore : Item116P2bCore) (hP2c : Item116P2c)
    (hCD : ResidueR1TwoStarCD) (hC38 : ResidueR1TwoStarCL38)
    (hCodd : ResidueR1TwoStarCOdd) : ResidueTR1 :=
  residueTR1_of_core hB KFacts.noDoubleComponentGL_holds hFC hFC3 h45 h113 hcore hP2c hCD hC38 hCodd

end Certified

end CFSG.RankThree.PartTwo.Sec11
