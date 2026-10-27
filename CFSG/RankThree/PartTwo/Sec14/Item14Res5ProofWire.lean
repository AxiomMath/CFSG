module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGenHJ
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesOne
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesM22
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesHJList
public import CFSG.RankThree.PartTwo.Sec14.Item14Res4ProofWire

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec13

theorem item142AllS14_of_leaves5
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hord : KS142J2Order) (hL3 : Step142LowerGenL3)
    (hT1 : Step142TypesOne) (hT2 : Step142TypesM22) (hT3 : Step142TypesHJ) : Item142AllS14 :=
  item142AllS14_of_leaves4 h131 h134 h48 h422 h45 (step142LowerGenNA7_of_L3 h131 hord hL3) hT1
    hT2 hT3

theorem item142AllS14_of_leaves6
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hord : KS142J2Order) (hL3 : Step142LowerGenL3)
    (hT1 : Step142TypesL3) (hT3 : Step142TypesHJ) : Item142AllS14 :=
  item142AllS14_of_leaves5 h131 h134 h48 h422 h45 hord hL3 (step142TypesOne_of h131 hT1)
    (step142TypesM22_of h131) hT3

theorem step142TypesS14_of_res5
    (h131 : Item131)
    (hT1 : Step142TypesL3) (hrig : KS142J2Rigid) : Step142TypesS14 :=
  step142TypesS14_of Sec13.sporadicModels131 (step142TypesOne_of h131 hT1)
    (step142TypesM22_of h131) (Res5TypesHJ.step142TypesHJ_of_rigid h131 hrig)

theorem item142AllS14_of_leaves7
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hord : KS142J2Order) (hrig : KS142J2Rigid)
    (hL3 : Step142LowerGenL3) (hT1 : Step142TypesL3) : Item142AllS14 :=
  item142AllS14_of_leaves6 h131 h134 h48 h422 h45 hord hL3 hT1
    (Res5TypesHJ.step142TypesHJ_of_rigid h131 hrig)

end CFSG.RankThree.PartTwo.Sec14
