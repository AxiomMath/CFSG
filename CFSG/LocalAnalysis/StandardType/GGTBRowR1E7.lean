module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Kg
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1E7Split
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1E7Det
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Datum

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggExcReflTBWeylDatumQFourOn_rowR1E7
    (hRig : GGLabelRigidInput) : GGTBDatumRowTarget GGTBRowR1E7 := by
  intro G _ _ p B Bs x L D J hHyp _ _ hL _
  obtain ⟨hp, -, -, -, -⟩ := hHyp.1.tableB_facts
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, f, ψ, hadm, hker, hrange, hpf⟩ :=
    ggR1E7_splitLie_tagged hp (ggInnerDiagOnLabel_r1Par_of_rowR1E7 hRig hHyp hL)
  have ht : StatedLieTag.E7 = .PSL ∨ StatedLieTag.E7 = .POmegaPlus ∨ StatedLieTag.E7 = .E6 ∨
      StatedLieTag.E7 = .E7 ∨ StatedLieTag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨h3, ψ', -, -, hpos⟩ := ggR1_kgPos_of_witness hHyp hadm hker hrange ht hpf
  exact ggR1_datum_of_tableBPos hp2 hHyp ht hadm h3 hpos (ggR1E7_det hp hp2)

end CFSG.StandardType

end
