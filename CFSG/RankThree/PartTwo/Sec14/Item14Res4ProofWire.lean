module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res4ProofA7
public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2Proof
public import CFSG.RankThree.PartTwo.Sec14.Item14Res3ProofPGL
public import CFSG.RankThree.PartTwo.KFacts.KS44Sz

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec13

theorem item142AllS14_of_leaves3
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hGen : Step142LowerGen) (hT1 : Step142TypesOne)
    (hT2 : Step142TypesM22) (hT3 : Step142TypesHJ) : Item142AllS14 :=
  item142AllS14_of_leaves2 h131 h134 h48 h422 h45 (step142PGLKer_of_res3 KFacts.kpSz) hGen step142L34Index hT1
    hT2 hT3

theorem item142AllS14_of_leaves4
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hN : Step142LowerGenNA7) (hT1 : Step142TypesOne)
    (hT2 : Step142TypesM22) (hT3 : Step142TypesHJ) : Item142AllS14 :=
  item142AllS14_of_leaves3 h131 h134 h48 h422 h45
    (step142LowerGen_of_a7 (step142LowerGenA7_of h131 Sec13.sporadicModels131) hN) hT1 hT2 hT3

end CFSG.RankThree.PartTwo.Sec14
