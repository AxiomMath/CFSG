module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofWire
public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofOrder
public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofRigid

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec13

theorem step142LowerGenHJ_of_131
    (h131 : Item131) : Step142LowerGenHJ :=
  step142LowerGenHJ_of h131 ks142J2Order

theorem step142LowerGenNA7_of_131
    (h131 : Item131) (hL3 : Step142LowerGenL3) : Step142LowerGenNA7 :=
  step142LowerGenNA7_of_L3 h131 ks142J2Order hL3

theorem step142TypesS14_of_131
    (h131 : Item131) (hT1 : Step142TypesL3) :
    Step142TypesS14 :=
  step142TypesS14_of_res5 h131 hT1 ks142J2Rigid

theorem item142AllS14_of_leaves8
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hL3 : Step142LowerGenL3) (hT1 : Step142TypesL3) : Item142AllS14 :=
  item142AllS14_of_leaves7 h131 h134 h48 h422 h45 ks142J2Order ks142J2Rigid hL3 hT1

end CFSG.RankThree.PartTwo.Sec14
