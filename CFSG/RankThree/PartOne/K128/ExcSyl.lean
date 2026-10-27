module

public import CFSG.RankThree.PartOne.K128.ExclSz
public import CFSG.RankThree.PartOne.K128.ExclExc
public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.RankThree.PartOne.K128.D4Syl
public import CFSG.RankThree.PartOne.K128.F4Syl

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG
open CFSG.Assembly.LowTwoRank (StatedLieTag)

set_option linter.unusedSectionVars false

theorem kf128SylTag_exceptional
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : Census3.ExceptionalRankFour) (t : StatedLieTag)
    (ht : t ∉ CFSG.Blueprint.classicalTags) : KF128SylTag t := by
  cases t with
  | PSL => exact absurd (by decide) ht
  | PSU => exact absurd (by decide) ht
  | PSp => exact absurd (by decide) ht
  | POmegaOdd => exact absurd (by decide) ht
  | POmegaPlus => exact absurd (by decide) ht
  | POmegaMinus => exact absurd (by decide) ht
  | G2 => exact kf128SylTag_G2
  | F4 => exact kf128SylTag_F4 hGA hExc
  | E6 => exact kf128SylTag_E6 hGA
  | E7 => exact kf128SylTag_E7 hGA hExc
  | E8 => exact kf128SylTag_E8 hGA hExc
  | twistedE6 => exact kf128SylTag_twistedE6 hGA
  | trialityD4 => exact kf128SylTag_trialityD4
  | twistedB2 => exact kf128SylTag_twistedB2
  | twistedG2 => exact kf128SylTag_twistedG2
  | twistedF4 => exact kf128SylTag_twistedF4
  | Tits => exact kf128SylTag_Tits

end CFSG.RankThree.PartOne.K128
