module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def S22_5_1K1 (D : Data G) (Ch : Choice2011 G) : Prop := D.k = 1 → S22_5_1 D Ch

theorem s22_5_1_of_branches {D : Data G} {Ch : Choice2011 G} (h1 : S22_5_1K1 D Ch)
    (h2 : D.k = 2 → S22_5_1 D Ch) : S22_5_1 D Ch := by
  have hk : D.k = 1 ∨ D.k = 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hk with hk | hk
  · exact h1 hk
  · exact h2 hk

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
