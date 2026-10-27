module

public import CFSG.RankThree.PartTwo.Sec15.Ronan153Big
public import CFSG.RankThree.PartTwo.Sec15.Gagen148FourKHolds
public import CFSG.RankThree.PartTwo.Sec13.Ronan137Holds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan153Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

section Closed


theorem item153BigR_of_closed
    (h135 : Item135) (h316 : Sec19.Item316) (h152 : Item152BigR) :
    Item153BigR := by
  obtain ⟨-, h48, -, -, -, h415, -, -, h134, -, h142⟩ := Ronan148M.closedInputs
  exact item153BigR_of h316 Ronan149.item149S14_holds Ronan148M.item148R_holds h134 h135
    Ronan137H.item137_holds h142 h48 h415 Ronan148M.concl142S14_holds
    Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds Ronan149.item1444S14_holds
    Ronan149.item145BotS14_holds (item148HJS14_of_wired Ronan148M.item148S14_holds) h152

end Closed

end CFSG.RankThree.PartTwo.Sec15.Ronan153Big
