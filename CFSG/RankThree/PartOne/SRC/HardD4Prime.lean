module

public import CFSG.RankThree.PartOne.SRC.Split
public import CFSG.RankThree.PartOne.SRC.ModelD4

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143


theorem noHardD4Prime : NoLowTwoRankSectionFor IsHardD4PrimeIndex := by
  refine noLowTwoRankSectionFor_of_rankFourCover fun i hi => ?_
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    obtain ⟨hq2, he⟩ := hi
    rename_i q
    exact ⟨q.p, q.prime_p, hq2, rankFourCover_trialityD4_prime q hv hq2 he⟩
  · exact (hi : False).elim

end CFSG.RankThree.PartOne.SRC
