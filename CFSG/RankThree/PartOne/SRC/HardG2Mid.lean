module

public import CFSG.RankThree.PartOne.SRC.Split
public import CFSG.RankThree.PartOne.SRC.ModelG2Tau

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143


theorem noHardG2Mid : NoLowTwoRankSectionFor IsHardG2MidIndex := by
  refine noLowTwoRankSectionFor_of_rankFourCover fun i hi => ?_
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    obtain ⟨hq2, he, h9⟩ := hi
    rename_i q
    exact ⟨q.p, q.prime_p, hq2, rankFourCover_G2_two q hv hq2 he h9⟩
  · exact (hi : False).elim

end CFSG.RankThree.PartOne.SRC
