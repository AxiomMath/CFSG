module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFourSplitDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFourNonsplitDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Inputs


theorem ggSecFiveBCoordBSparseTwDFour_of_split_nonsplit
    (hSplit : GGSecFiveBCoordBSparseTwDFourSplitInput)
    (hNonsplit : GGSecFiveBCoordBSparseTwDFourNonsplitInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hBJ : BMaxJoinInput) :
    GGSecFiveBCoordBSparseOn fun n _ lab => n = 4 ∧ lab.n ≠ 1 ∧ lab.tag = .twD := by
  have hS := hSplit hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ
  have hN := hNonsplit hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hSpC hSpSpC hOmC hD
  have hLab' : GGInnerDiagOnLabel (fun p lab =>
      (GGSecFiveBCoordBLabel n p lab ∧
          (n = 4 ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n - 1)) ∨
        (GGSecFiveBCoordBLabel n p lab ∧
          (n = 4 ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1))) p Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ hPl => ⟨?_, hPl.2⟩) hLab
    obtain ⟨⟨hl, h4, h1, ht⟩, -⟩ := hPl
    have hl' := hl
    rcases hl' with ⟨ht', -⟩ | ⟨-, -, hsplit | ⟨-, hnon⟩⟩ | ⟨ht', -⟩ | ⟨ht', -⟩
    · rcases ht' with ht' | ht' <;> simp [ht] at ht'
    · exact Or.inl ⟨hl, h4, h1, ht, hsplit⟩
    · exact Or.inr ⟨hl, h4, h1, ht, hnon⟩
    · simp [ht] at ht'
    · simp [ht] at ht'
  rcases hLab'.elim_or with h | h
  · exact hS G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hSpC hSpSpC hOmC hD
  · exact hN G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hSpC hSpSpC hOmC hD

end Inputs

end CFSG.StandardType

end
