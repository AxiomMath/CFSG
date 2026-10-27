module

public import CFSG.Quasithin.EmptyFaithful.S1421QA23Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Rows

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem core3HeLnTwo_of_a312
    (hS : QA23.FactSporadicOrders) (hM : Vol2.Ch11.SecB.FactMathieuOrders)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h37 : A37ForSQTK) : Core3HeLnTwo := by
  intro G _ _ T M H K1 L M₁ c _ _ _ hX
  exact c.false_of_isPSL_four_five hS hM hP h36 h312 h37 hX

theorem core3HeBorel_of_a312
    (h56 : AsB56) (hcover : AsA36NoOddCover) (hG2 : FactG2Cayley) (h210 : Lemma14210)
    (hS : QA23.FactSporadicOrders) (hM : Vol2.Ch11.SecB.FactMathieuOrders)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h37 : A37ForSQTK) (hA7 : Core3HeA7) : Core3HeBorel :=
  core3HeBorel_of_inputs h56 hcover hG2 h210 (core3HeLnTwo_of_a312 hS hM hP h36 h312 h37) hA7

end CFSG.Quasithin
