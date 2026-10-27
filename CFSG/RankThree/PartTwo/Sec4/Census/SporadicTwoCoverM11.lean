module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.GH74.KGroups.CoverM11

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint

theorem noRankThreeTwoCover_m11 :
    NoRankThreeTwoCover (Spor .M11) := by
  intro J _ _ hJ
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact absurd hJ (not_isTwoCover_of_noTwoCover
    (CFSG.GH74.KGroups.M11.noTwoCover_M11 (Spor .M11) ⟨b.symm⟩))

end CFSG.RankThree.PartTwo.Sec4.Census
