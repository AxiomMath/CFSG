module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y143Defs
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y143Point
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

theorem y1SecondFormExcl_of_k143Excl (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (hK : K143Excl) : Y1SecondFormExcl := by
  intro G _ _ A c L hR hW B hBA hfree Yc hYc ha
  by_contra hne
  obtain ⟨hY4, hZ3, x, hx⟩ :=
    Gagen155Y143.exists_is143Point h1 h2 h43 hin hR hW hBA hfree hYc ha hne
  exact hK _ hY4 hYc.1 hZ3 x hx

end CFSG.RankThree.PartTwo.Sec15
