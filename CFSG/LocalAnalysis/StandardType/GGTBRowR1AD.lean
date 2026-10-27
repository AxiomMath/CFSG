module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Kg
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1ADSplit
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1ADDet

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggExcReflTBWeylDatumQFourOn_rowR1AD
    (hRig : GGLabelRigidInput) :
    GGTBDatumRowTarget
      (fun p lab => (GGTBRowR1A p lab ∧ ¬ p ∣ lab.rank + 1) ∨ GGTBRowR1D p lab) := by
  intro G _ _ p B Bs x L D J hHyp _ _ hL _
  obtain ⟨hp, -, -, -, -⟩ := hHyp.1.tableB_facts
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, n, f, ψ, htag, hadm, hker, hrange, hpf⟩ :=
    ggR1AD_splitLie_tagged hp hp2 (ggInnerDiagOnLabel_r1Par_of_rowR1AD hRig hHyp hL)
  have ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 := by
    rcases htag with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  obtain ⟨h3, ψ', -, -, hpos⟩ := ggR1_kgPos_of_witness hHyp hadm hker hrange ht hpf
  exact ggR1_datum_of_tableBPos hp2 hHyp ht hadm h3 hpos (ggR1AD_det hp2 htag)

end CFSG.StandardType

end
