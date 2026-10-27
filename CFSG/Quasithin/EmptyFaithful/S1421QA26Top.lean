module

public import CFSG.Quasithin.EmptyFaithful.S1421QA26Core
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Top

public section

namespace CFSG.Quasithin

theorem core3HeBorel_of_inputs_a7
    (h56 : AsB56) (hcover : AsA36NoOddCover) (hG2 : FactG2Cayley) (h210 : Lemma14210)
    (h209 : Lemma14209Used) (hS : QA23.FactSporadicOrders)
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hP : Vol2.Ch11.SecA.FactL2Parabolic)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h37 : A37ForSQTK) : Core3HeBorel :=
  core3HeBorel_of_a312 h56 hcover hG2 h210 hS hM hP h36 h312 h37
    (core3HeA7_of_inputs h56 h210 h209)

theorem core3HeSyl_of_inputs_a7
    (h56 : AsB56) (hcover : AsA36NoOddCover) (hG2 : FactG2Cayley) (h210 : Lemma14210)
    (h209 : Lemma14209Used) (hS : QA23.FactSporadicOrders)
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hP : Vol2.Ch11.SecA.FactL2Parabolic)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h37 : A37ForSQTK) : Core3HeSyl :=
  core3HeSyl_of_borel (core3HeBorel_of_inputs_a7 h56 hcover hG2 h210 h209 hS hM hP h36 h312 h37)

end CFSG.Quasithin
