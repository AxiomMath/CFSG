module

public import CFSG.RankThree.PartOne.SRC.Split
public import CFSG.RankThree.PartOne.SRC.ModelReeTau

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143


theorem noHardRee : NoLowTwoRankSectionFor IsHardReeIndex := by
  refine noLowTwoRankSectionFor_of_rankFourCover_finite fun i hi hfin => ?_
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    rename_i m
    exact ⟨3, Nat.prime_three, by norm_num, rankFourCover_reeG2 m hv hi⟩
  · exact (hi : False).elim

end CFSG.RankThree.PartOne.SRC
