module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Fams
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331ClIdx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti

theorem k331_classicalLow : K331Fam K331ClassicalLow := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact False.elim hi
  · exact False.elim hi
  · cases d with
    | A r q =>
      by_cases hp : q.p = 2
      · have hr : r = 1 := by
          rcases hi with h | ⟨h, -⟩
          · exact h
          · exact absurd hp h
        subst hr
        exact k331Idx_A_one_even hv hp
      · refine k331Idx_A_odd hv ?_ hp
        rcases hi with h | ⟨-, h | ⟨h | h, -⟩⟩ <;> omega
    | twistedA r q =>
      obtain ⟨hp, h⟩ := hi
      exact k331Idx_twistedA_odd hv (by rcases h with h | ⟨h | h, -⟩ <;> omega) hp
    | B r q =>
      obtain ⟨hr, hp⟩ := hi
      subst hr
      exact k331Idx_B_two hv hp
    | _ => exact False.elim hi
  · exact False.elim hi

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
