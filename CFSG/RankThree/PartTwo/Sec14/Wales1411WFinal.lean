module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WRoute
public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreON
public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA5J2
public import CFSG.RankThree.PartTwo.Sec15.Gagen148FourKHolds
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LHessFinal
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA7
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA5A5
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA6A5
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA6A6

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

theorem ks1411HJCore_of_L37
    (hL : KS1411HJCoreL37) :
    KS1411HJCore :=
  ks1411HJCore_of_types ks1411HJCoreON ks1411HJCoreA6A6 ks1411HJCoreA6A5 ks1411HJCoreA5A5
    ks1411HJCoreA7 hL ks1411HJCoreA5J2

section Route


theorem item1411_1R_of_L37
    (hL : KS1411HJCoreL37) : Item1411_1R := by
  obtain ⟨h45, h48, -, h422, -, -, -, h131, h134, -, h142⟩ := Ronan148M.closedInputs
  exact item1411_1R_of_hjkfact h131 h142 Ronan148M.item143QS14_holds
    Sec15.Proof148FourK.item146S14_holds Ronan148M.item148R_holds Ronan149.item145BotS14_holds
    h134 h48 h422 h45 Sec4.Ronan148L.kl3HessTori_holds (ks1411HJCore_of_L37 hL)

end Route

end CFSG.RankThree.PartTwo.Sec14
