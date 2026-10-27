module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Good

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def Sec7CoreOdd {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → IsStronglyPEmbedded q D.M →
    ∃ k : Section7.Sec7Core4 G, k.M = D.M ∧ k.p = q ∧ (5 ≤ q → k.KIDExcluded ∧ k.Step75)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
