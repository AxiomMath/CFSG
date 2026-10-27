module

public import CFSG.RankThree.PartTwo.Sec15.Ronan154BigPi
import CFSG.RankThree.PartTwo.Sec15.Ronan154BigMem
import CFSG.RankThree.PartTwo.Sec15.Ronan154Big159
public import CFSG.RankThree.PartTwo.Sec15.Ronan155BigFinal
import CFSG.RankThree.PartTwo.Sec15.Ronan154BigY4

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan154Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

section Final


theorem item159R_of_big154
    (h135 : Item135) (h316 : Sec19.Item316) (h152 : Item152BigR) :
    Item159R := by
  obtain ⟨h45, h48, -, h422, -, -, -, h131, h134, -, -⟩ := Ronan148M.closedInputs
  have h148 : Item148R := Ronan148M.item148R_holds
  have hbot : Item145BotS14 := Ronan149.item145BotS14_holds
  have h149 : Sec16.Item149S14 := Ronan149.item149S14_holds
  have h146 : Item146S14 := Proof148FourK.item146S14_holds
  have h142 : Item142R := item142R_of_wired item142AllS14_holds
  have hS : Y4CoreMemSolvR := LiebeckClosed.y4CoreMemSolvR_holds
  have hRead : Y4CoreReadR := Read148Perf.y4CoreReadR_from_item148R KFacts.kpSz hbot h148
  have h138 : Item138N := Ronan138S.item138_of_frontier
  have hodd : Step159Y0Odd := step159Y0Odd_of_nhj hRead h149 hS h134 h48 h146
    item1411_3R_holds (step159Y0NotTrans_of h135 h138 h142 ks159TorusPair)
  have hY0 : Step159Y0 := step159Y0_of (h135 := h135) (h142 := h142)
    (hgen := step159Y0Gen_of (h138 := h138)
      (hgen := ks1517Gen_of (h := ks1517CentGen_of (hU := ks1517SeitzU)))) (hodd := hodd)
  exact item159R_of_res2_big h131 (rank3II_13_3_of h131 h422 h45) h149
    (Ronan153Big.item153BigR_of_closed h135 h316 h152) item1411_1R_holds (item146R_of_S14 h146)
    hY0 (step159WT_of (h142 := h142))
    (step159ClaimK_of_nhj hRead h149 hS h134 h48 hbot
      (step159ClaimKY0_of h134 h48 h148 LiebeckClosed.step159FiveR_holds))
    (y4BigNHJR_of h134 h48 Ronan148C.step148Core_holds Ronan148M.step148Point_holds
      Ronan148M.step148KType_holds)

theorem item155wJ2R_of_big154
    (h135 : Item135) (h316 : Sec19.Item316) (h152 : Item152BigR)
    (hst : StellmacherKP) (hfr : Step155FrattiniNWPR) : Item155wJ2R :=
  Ronan155Big.item155wJ2R_of_big_final h135 h316 h152
    (item154PiR_of_item159R (item159R_of_big154 h135 h316 h152)) hst hfr

end Final

end CFSG.RankThree.PartTwo.Sec15.Ronan154Big
