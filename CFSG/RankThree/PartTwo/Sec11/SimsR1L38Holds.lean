module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1L38TwoStar
public import CFSG.RankThree.PartTwo.Sec11.SimsR1L38LF
public import CFSG.RankThree.PartTwo.Sec11.SimsR1L38Aut
public import CFSG.RankThree.PartTwo.Sec11.SimsR1L38Faithful
public import CFSG.RankThree.PartTwo.Sec11.SimsR1L38Solvable
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed

public section

namespace CFSG.RankThree.PartTwo.Sec11


theorem residueR1TwoStarCL38_holds
    : ResidueR1TwoStarCL38 :=
  residueR1TwoStarCL38_of_lf SimsR1.l38AutFacts_holds Sec4.rank3II_4_5
    (fun _ _ _ _ _ _ _ _ _ _ h hT hL => SimsR1.lfAt_c_L38 SimsR1.l38FaithfulFix_holds
      (SimsR1.l38SolvableFix_of_faithful SimsR1.l38FaithfulFix_holds) Sec4.rank3II_4_5 h hT hL)

end CFSG.RankThree.PartTwo.Sec11
