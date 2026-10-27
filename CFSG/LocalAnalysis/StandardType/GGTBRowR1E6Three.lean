module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1E6Split
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Cond

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggExcReflTBWeylDatumQFourOn_rowR1E6Three
    (hRig : GGLabelRigidInput)
    (hnc : GGTBJNoncommRowTarget (fun p lab => GGTBRowR1E6 p lab ∧ p = 3)) :
    GGTBDatumRowTarget (fun p lab => GGTBRowR1E6 p lab ∧ p = 3) := by
  refine ggTBDatumRowTarget_of_noncomm (fun {G} _ _ {p} {B Bs x L D J} hHyp hL => ?_) hnc
  obtain ⟨hp, -, -, -, -⟩ := hHyp.1.tableB_facts
  have hL6 : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR1E6 p lab) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.1, hP.1.2.1⟩, hP.2⟩) hL
  obtain ⟨n, f, ψ, hadm, hker, hrange, hpf⟩ :=
    ggR1E6_splitLie_tagged hp (ggInnerDiagOnLabel_r1Par_of_rowR1E6 hRig hHyp hL6)
  exact ⟨.E6, n, f, ψ, Or.inr (Or.inr (Or.inl rfl)), hadm, hker, hrange, hpf⟩

end CFSG.StandardType

end
