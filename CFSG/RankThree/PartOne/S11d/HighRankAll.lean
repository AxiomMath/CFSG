module

public import CFSG.RankThree.PartOne.S11d.HighRankPSU
public import CFSG.RankThree.PartOne.S11d.HighRankClassical
public import CFSG.RankThree.PartOne.S11d.HighRankExc

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem TCX.highRankFalse_of_lowRank {t : StatedLieTag} (h : ∀ n, TCX.LowRank t n) :
    TCX.HighRankFalse t :=
  fun _ _ _ _ _ n _ _ _ _ _ _ _ _ _ hnl => hnl (h n)


theorem TCX.highRankFalse_all : ∀ t : StatedLieTag, TCX.HighRankFalse t
  | .PSL => TCX.highRankFalse_of_lowRank fun _ => trivial
  | .PSU => TCX.highRankFalse_PSU
  | .PSp => TCX.highRankFalse_PSp
  | .POmegaOdd => TCX.highRankFalse_of_lowRank fun _ => trivial
  | .POmegaPlus => TCX.highRankFalse_POmegaPlus
  | .POmegaMinus => TCX.highRankFalse_POmegaMinus
  | .G2 => TCX.highRankFalse_of_lowRank fun _ => trivial
  | .F4 => TCX.highRankFalse_F4
  | .E6 => TCX.highRankFalse_E6
  | .E7 => TCX.highRankFalse_E7
  | .E8 => TCX.highRankFalse_E8
  | .twistedE6 => TCX.highRankFalse_twistedE6
  | .trialityD4 => TCX.highRankFalse_of_lowRank fun _ => trivial
  | .twistedB2 => TCX.highRankFalse_of_lowRank fun _ => trivial
  | .twistedG2 => TCX.highRankFalse_of_lowRank fun _ => trivial
  | .twistedF4 => TCX.highRankFalse_of_lowRank fun _ => trivial
  | .Tits => TCX.highRankFalse_of_lowRank fun _ => trivial

end CFSG.RankThree.PartOne
