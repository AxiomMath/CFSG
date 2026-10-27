module

public import CFSG.RankThree.PartOne.KF.F128Sp
public import CFSG.RankThree.PartOne.KF.F128SU
public import CFSG.RankThree.PartOne.KF.F128SL
public import CFSG.RankThree.PartOne.KF.F128Omega
public import CFSG.RankThree.PartOne.K128.ExcSyl

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false


theorem kf128Syl_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) (hSpin : Census3.SpinRankFour) : KF128Syl :=
  kf128Syl_of_tags fun t => by
    by_cases ht : t ∈ CFSG.Blueprint.classicalTags
    · cases t
      · exact kf128SylTag_PSL hGA
      · exact kf128SylTag_PSU hGA
      · exact kf128SylTag_PSp hGA
      · exact kf128SylTag_POmegaOdd
      · exact kf128SylTag_POmegaPlus hGA hSpin
      · exact kf128SylTag_POmegaMinus hGA hSpin
      all_goals exact absurd ht (by decide)
    · exact K128.kf128SylTag_exceptional hGA hExc t ht

end CFSG.RankThree.PartOne
