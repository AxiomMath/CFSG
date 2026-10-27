module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Transv
public import CFSG.RankThree.PartTwo.Sec21.FF84S4A5Odd
public import CFSG.RankThree.PartTwo.Sec21.FF84S49Two
public import CFSG.RankThree.PartTwo.Sec21.FF84S49ASix

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

theorem A_transv_holds : A_transv_stmt := by
  intro Y hY x hx hne h1 h2
  rcases hY with rfl | rfl
  · exact A_transv_Ua x hx hne h1 h2
  · exact A_transv_Ub x hx hne h1 h2

theorem A_cent_A5_odd_holds : A_cent_A5_odd_stmt :=
  fun K' hK e5 c hc hcK => A_cent_A5_odd K' hK e5 c hc hcK

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
