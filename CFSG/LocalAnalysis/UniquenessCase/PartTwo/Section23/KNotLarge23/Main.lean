module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Sz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineKNotLarge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

theorem kNotLarge23_of_sz
    (hSz : ∀ (Q : Type) [Group Q] [Finite Q] (a : ℕ), IsSz Q a →
      ∀ (N : Subgroup Q) [N.Normal] (n : ℕ), 3 ≤ n →
        ¬ (IsSLn (Q ⧸ N) 3 n ∨ IsSp4 (Q ⧸ N) n ∨ IsU4 (Q ⧸ N) n)) :
    KNotLarge23 := by
  refine ⟨?_, ?_⟩
  · intro Q _ _ hQ N _ n hn
    rcases hQ with ⟨a, hL2 | hSz'⟩ | ⟨p, hp, hp2, hL2o⟩ | hJ1
    · exact knl_l2 hL2 N hn
    · exact hSz Q a hSz' N n hn
    · exact knl_l2odd hp hp2 hL2o N hn
    · exact knl_j1 hJ1 N hn
  · intro X _ _ n hn hX
    exact knl_square hn hX

theorem kNotLarge23_holds : KNotLarge23 :=
  kNotLarge23_of_sz fun _ _ _ _ hQ N _ _ hn => knl_sz hQ N hn

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
