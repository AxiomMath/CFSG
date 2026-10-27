module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofWire
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessList
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofU38
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofInner
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofGenNine
public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofWireHJ

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec13

theorem step142LowerGenL3_of_res8
    (h131 : Item131)
    (h9 : KS142L3HessGenNine) (hPGL : Step142LowerGenL3PGL) : Step142LowerGenL3 :=
  step142LowerGenL3_of_131 h131 h9 ks142U38Alpha hPGL

theorem step142TypesL3_of_pow
    (h131 : Item131) (hPow : Step142TypesL3InnerPow)
    (hTPGL : Step142TypesL3PGL) : Step142TypesL3 :=
  step142TypesL3_of h131 ks142L3HessList (step142TypesL3InnerRest_of_pow hPow) hTPGL

theorem item142AllS14_of_leaves10
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h9 : KS142L3HessGenNine) (hPGL : Step142LowerGenL3PGL)
    (hPow : Step142TypesL3InnerPow) (hTPGL : Step142TypesL3PGL) : Item142AllS14 :=
  item142AllS14_of_leaves8 h131 h134 h48 h422 h45 (step142LowerGenL3_of_res8 h131 h9 hPGL)
    (step142TypesL3_of_pow h131 hPow hTPGL)

theorem item142AllS14_of_leaves11
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h9 : KS142L3HessGenNineModel) (hPGL : Step142LowerGenL3PGL)
    (hPow : Step142TypesL3InnerPow) (hTPGL : Step142TypesL3PGL) : Item142AllS14 :=
  item142AllS14_of_leaves10 h131 h134 h48 h422 h45 (ks142L3HessGenNine_of_model h9) hPGL hPow
    hTPGL

end CFSG.RankThree.PartTwo.Sec14
