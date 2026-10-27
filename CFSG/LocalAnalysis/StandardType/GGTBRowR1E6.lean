module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Kg
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1E6Split
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1E6Det
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Datum

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggExcReflTBWeylDatumQFourOn_rowR1E6Ne3
    (hRig : GGLabelRigidInput) : GGTBDatumRowTarget GGTBRowR1E6Ne3 := by
  intro G _ _ p B Bs x L D J hHyp _ _ hL _
  obtain ⟨hp, -, -, -, -⟩ := hHyp.1.tableB_facts
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  have hp3 : p ≠ 3 := ggTBRowR1E6Ne3_p_ne_three hL
  haveI : Fact p.Prime := ⟨hp⟩
  have hL6 : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR1E6 p lab) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.1, hP.1.2.1⟩, hP.2⟩) hL
  obtain ⟨n, f, ψ, hadm, hker, hrange, hpf⟩ :=
    ggR1E6_splitLie_tagged hp (ggInnerDiagOnLabel_r1Par_of_rowR1E6 hRig hHyp hL6)
  have ht : StatedLieTag.E6 = .PSL ∨ StatedLieTag.E6 = .POmegaPlus ∨ StatedLieTag.E6 = .E6 ∨
      StatedLieTag.E6 = .E7 ∨ StatedLieTag.E6 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨h3, ψ', -, -, hpos⟩ := ggR1_kgPos_of_witness hHyp hadm hker hrange ht hpf
  exact ggR1_datum_of_tableBPos hp2 hHyp ht hadm h3 hpos (ggR1E6_det hp hp3)

end CFSG.StandardType

end
