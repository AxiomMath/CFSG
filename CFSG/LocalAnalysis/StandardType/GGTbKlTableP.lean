module

public import CFSG.LocalAnalysis.StandardType.GGTbKlJ
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
open CFSG.RankThree.PartOne.KCOrthogonal

private lemma tbkls6_labelJ_case {labJ' : LargeEvenLabel}
    (hiso : GGLabelIso ⟨.A, 3, 1⟩ labJ') :
    labJ' = ⟨.A, 3, 1⟩ ∨ labJ' = ⟨.D, 3, 1⟩ := by
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h
  · exact Or.inl h.symm
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by simp)
  · exact Or.inr h.2
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.2 (by simp)

theorem ggTablePRow_three_a3_one {labJ labK : LargeEvenLabel}
    (hJ : labJ = ⟨.A, 3, 1⟩ ∨ labJ = ⟨.D, 3, 1⟩) (hrow : GGTablePRow 3 labJ labK) :
    labK = ⟨.A, 5, 1⟩ ∨ labK = ⟨.twD, 4, 1⟩ := by
  rcases hJ with rfl | rfl
  · exact Or.inl (by simpa [GGTablePRow] using hrow)
  · exact Or.inr (by simpa [GGTablePRow] using hrow)

theorem ggF4QTwoEndsKlInput_of_tableP
    (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) : GGF4QTwoEndsKlInput := by
  intro G _ _ B Bs x L D J hR _hWc _hq y K hNb _hW hL
  obtain ⟨hJlab, _hJZ⟩ := ggF4QTwoOmegaEnd_label_J hR.1 hR.2.2.1.1 hNb hL
  obtain ⟨labK, hΛK, hKhas, -⟩ :=
    largeEvenMarking_exists_hasLabel (hR.2.2.1.2 y K hNb)
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hJ'has, hK'has⟩ :=
    hTP G 3 B Bs x L D J y K hR.1 hR.2.2.1.1 (hR.2.2.1.2 y K hNb) hNb
      ⟨.A, 3, 1⟩ labK (by unfold LargeEvenInLambda2; decide) hΛK ⟨rfl, rfl, rfl, by norm_num⟩
      hJlab hKhas
  have hiso : GGLabelIso ⟨.A, 3, 1⟩ labJ' :=
    ggLabelRigidInput_holds ⟨.A, 3, 1⟩ labJ' (↥J ⧸ Subgroup.center ↥J)
      (by unfold LargeEvenInLambda2; decide) hΛJ' hJlab hJ'has
  have hJ'case : labJ' = ⟨.A, 3, 1⟩ ∨ labJ' = ⟨.D, 3, 1⟩ := tbkls6_labelJ_case hiso
  have hK'case : labK' = ⟨.A, 5, 1⟩ ∨ labK' = ⟨.twD, 4, 1⟩ :=
    ggTablePRow_three_a3_one hJ'case hrow
  have hKmark : LargeEvenMarking ↥K (fun lab' _ _ _ _ _ => lab' = labK') :=
    largeEvenMarking_mono (fun lab' R' _ I F θ hh => hh.1)
      (ggInnerDiagOn_relabel ggLabelRigidInput_holds (hR.2.2.1.2 y K hNb) hΛK' hK'has)
  rcases hK'case with hAK | hDK
  · left
    refine largeEvenMarking_mono ?_ hKmark
    intro lab R _ I F θ hh
    rw [hh, hAK]
    exact ⟨rfl, rfl, rfl⟩
  · right
    refine largeEvenMarking_mono ?_ hKmark
    intro lab R _ I F θ hh
    rw [hh, hDK]
    exact ⟨rfl, rfl, rfl⟩

end CFSG.StandardType

end
