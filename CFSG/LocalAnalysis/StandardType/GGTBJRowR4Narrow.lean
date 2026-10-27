module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Row
public import CFSG.LocalAnalysis.StandardType.GGTBJNaWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTBJNoncommReflOn_of_split (S T : ℕ → LargeEvenLabel → Prop)
    (hST : GGTBJNoncommReflOn fun p lab => S p lab ∧ T p lab)
    (hSN : GGTBJNoncommReflOn fun p lab => S p lab ∧ ¬ T p lab) :
    GGTBJNoncommReflOn S := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  have hL' : GGInnerDiagOnLabel (fun p lab => (S p lab ∧ T p lab) ∨ (S p lab ∧ ¬ T p lab))
      p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨hs, hP⟩ =>
      ⟨(em (T p _)).elim (fun h => Or.inl ⟨hs, h⟩) (fun h => Or.inr ⟨hs, h⟩), hP⟩) hL
  rcases hL'.elim_or with h | h
  · exact hST G p B Bs x L D J hHyp hq hN h
  · exact hSN G p B Bs x L D J hHyp hq hN h

theorem ggTBJNoncommReflOn_of_rowR4
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGTBJNoncommReflOn fun p lab => S p lab ∧ lab.tag ≠ .F4) :
    GGTBJNoncommReflOn S :=
  ggTBJNoncommReflOn_of_split S GGTBRowR4
    ((ggTBJNoncommReflOn_of_naWeyl (ggTBJNaWeylQFourOn_rowR4 hRig)).mono
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
