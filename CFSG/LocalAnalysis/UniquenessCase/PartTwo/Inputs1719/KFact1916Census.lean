module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

theorem list19_16_5_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : List19_16_5 Q) : List19_16_5 Q' := by
  rcases h with (⟨m, h⟩ | ⟨s, hs5, hs7, h⟩) | hf | h | h
  · refine Or.inl (Or.inl ⟨m, ?_⟩)
    rcases h with h | h | h | h | h | h | h
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
    · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))
    · exact Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (CFSG.Blueprint.LieModel.of_mulEquiv e h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (CFSG.Blueprint.LieModel.of_mulEquiv e h))))))
  · exact Or.inl (Or.inr ⟨s, hs5, hs7, CFSG.Blueprint.LieModel.of_mulEquiv e h⟩)
  · obtain ⟨f⟩ := hf
    exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · exact Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h)))

@[expose] def K_19_16_census : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsQuasisimple Y → CFSG.pCore 2 Y = ⊥ →
    CFSG.AGLEmbedding.IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y) →
    (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup Y) ≤ 3) →
    ∀ (J : Subgroup Y) (T : Sylow 2 Y), J ≠ ⊤ →
      Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J →
      Nat.card (CFSG.Open.pCoreOf 2 J) ≠ Nat.card T →
      List19_16_5 (Y ⧸ Subgroup.center Y)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
