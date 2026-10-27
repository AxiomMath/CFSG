module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

import CFSG.LocalAnalysis.UniquenessCase.UC22ListB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (IsLieOver)
open CFSG.LocalAnalysis.RankThreeUC (Asc1930ListB)

theorem isCalL0_iff_asc1930ListB (X : Type) [Group X] : IsCalL0 X ↔ Asc1930ListB X := by
  constructor
  · rintro (⟨n, hn, t, m, h⟩ | h | h | h | h | h | h)
    · exact Or.inl ⟨t, m, n, hn, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · rintro (⟨t, m, n, hn, h⟩ | h | h | h | h | h | h)
    · exact Or.inl ⟨n, hn, t, m, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))


theorem isCalL0_nonabelian_not_sectionalTwoRankLE (L : Type) [Group L] [Finite L]
    (hL : IsCalL0 L) :
    (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2 := by
  obtain ⟨_, h3, hnab⟩ :=
    uc22lb_listB_facts listBExceptionalFacts ((isCalL0_iff_asc1930ListB L).1 hL)
  refine ⟨hnab, fun hsec => ?_⟩
  have h2 := hsec.twoRank_le
  unfold CFSG.Open.twoRank at h2
  omega

end CFSG.LocalAnalysis.WeakClosure81
