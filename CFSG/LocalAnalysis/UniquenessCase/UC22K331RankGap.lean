module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Fams
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankGapE6
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankGapU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti

section Certified


theorem k331_rankGap : K331Fam K331RankGap := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact False.elim hi
  · exact False.elim hi
  · cases d with
    | twistedE6 q => exact k331Idx_twistedE6 q hv
    | twistedA r q =>
      obtain ⟨h5, hc⟩ := hi
      exact k331Idx_twistedA_of_five_le hv h5 hc
    | _ => exact False.elim hi
  · exact False.elim hi

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
