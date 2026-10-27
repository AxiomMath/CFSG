module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU3
import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL2
import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL3
import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL33
import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU33

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Item434CharThree

section Families


theorem item434CharThree_of_remainder (hU : CharThreeU3CenterFree)
    (hG2 : Item434CharThreeG2) (hL4 : Item434CharThreeL4) (hU4 : Item434CharThreeU4)
    (hRee : Item434CharThreeRee) : Item434CharThree :=
  item434CharThree_of_split item434CharThreeL2Three item434CharThreeL2Nine
    item434CharThreeL2Large item434CharThreeL3Three item434CharThreeU3Three
    item434CharThreeL3Large (item434CharThreeU3Large_of_centerFree hU) hG2 hL4 hU4 hRee

theorem item434CharThree_of_griess
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hG2 : Item434CharThreeG2) (hL4 : Item434CharThreeL4) (hU4 : Item434CharThreeU4)
    (hRee : Item434CharThreeRee) : Item434CharThree :=
  item434CharThree_of_remainder (charThreeU3CenterFree_of_griess hGA) hG2 hL4 hU4 hRee

end Families

end CFSG.RankThree.PartTwo.Sec4
