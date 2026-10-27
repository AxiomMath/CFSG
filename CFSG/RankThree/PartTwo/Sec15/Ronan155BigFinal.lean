module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155BigRoute
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigClosed
public import CFSG.RankThree.PartTwo.Sec15.Ronan155W315QRoute
public import CFSG.RankThree.PartTwo.Sec14.Item1411_3RHolds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

section Final


theorem item155wJ2R_of_big_final
    (h135 : Item135) (h316 : Sec19.Item316)
    (h152 : Item152BigR) (h154 : Item154PiR) (hst : StellmacherKP)
    (hfr : Step155FrattiniNWPR) : Item155wJ2R := by
  obtain ⟨-, h48, -, -, -, -, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact item155wJ2R_of_big h152 (Ronan153Big.item153BigR_of_closed h135 h316 h152) h154 h316 hst
      (Ronan155W315.step155W315PR_of_v4 KFacts.kpSz Ronan148M.item148R_holds
          Ronan148M.concl142S14_holds Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
          Ronan149.item1444S14_holds Ronan149.item145BotS14_holds Ronan149.item149S14_holds
          item142AllS14_holds h134 h48 LiebeckClosed.y4CoreMemSolvR_holds) hfr

end Final

end CFSG.RankThree.PartTwo.Sec15.Ronan155Big
