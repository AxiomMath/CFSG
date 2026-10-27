module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108Rows
public import CFSG.Open.SplitBNPair
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigRow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

theorem k108RowX_of_splitBN {F : (S : Type) → [Group S] → Prop}
    (hBN : ∀ (S : Type) [Group S] [Finite S], F S → IsSimpleGroup S →
      ∃ B N : Subgroup S, CFSG.ASVolI.ChIJK.IsSplitBNPair 2 B N ∧ B ≠ ⊤) : K108RowX F := by
  intro Gh _ _ S hSn hS _ _ hF T X hT hX hXodd _ hXT M hTM hXM hstar
  haveI := hSn
  haveI := hS
  obtain ⟨B, N, hB, hBtop⟩ := hBN ↥S hF hS
  exact k108big_rowX_strong S hB hBtop hT hX hXodd hXT hTM hXM hstar

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
