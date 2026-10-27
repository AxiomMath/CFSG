module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.GH74.Generic.GKFSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint

theorem noRankThreeTwoCover_j1 : NoRankThreeTwoCover (Spor .J1) := by
  intro J _ _ hJ
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  exact absurd hJ (not_isTwoCover_of_noTwoCover
    (CFSG.GH74.Generic.noTwoCover_J1_of_walter (Spor .J1) ⟨b.symm⟩))

end CFSG.RankThree.PartTwo.Sec4.Census
