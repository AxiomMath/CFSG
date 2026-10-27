module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrCore
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrGate
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrGenerated

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open TableB

theorem ggTypeANbrModelInput_of_known (hCD : GGTypeACompatDiagBInput) (hRig : GGLabelRigidInput)
    (hTB : GGNbrTableBWeylInput) (hC : GGNbrTableBCardInput) (hO : GGNbrTableBOrderRestInput)
    (hF : GGNbrFrameInput) (hTP : GGTypeANbrTablePInput) : GGTypeANbrModelInput := by
  intro G _ _ p B Bs x L D J n f y K h y' K' hK' hW
  exact (ggTypeANbr_core hCD hRig hTB hC hO hF h (hTP G p B Bs x L D J n f y K h) hK'
    (m := n + 1) ⟨Nat.le_succ n, le_rfl⟩ hW).2

theorem ggTypeANbrConjGenInput_of_known (hCD : GGTypeACompatDiagBInput)
    (hRO : GGTypeAReflOverInput) (hRig : GGLabelRigidInput) (hTB : GGNbrTableBWeylInput)
    (hC : GGNbrTableBCardInput) (hO : GGNbrTableBOrderRestInput) (hF : GGNbrFrameInput)
    (hTP : GGTypeANbrTablePInput) : GGTypeANbrConjGenInput := by
  intro G _ _ p B Bs x L D J n f y K h y' K' hK'
  obtain ⟨m, hnm, hmn, hgate⟩ := ggTypeANbr_gate hCD hRO h hK'
  obtain ⟨hmeq, hmod⟩ := ggTypeANbr_core hCD hRig hTB hC hO hF h
    (hTP G p B Bs x L D J n f y K h) hK' ⟨hnm, hmn⟩ hgate
  subst hmeq
  have h' : GGTypeANbrCfg p B Bs x L D J n f y' K' := by
    obtain ⟨hcfg, hOp, hInn, hNoTr, hmodL, hpq, hn, hsc, -, -, -, hAll⟩ := h
    exact ⟨hcfg, hOp, hInn, hNoTr, hmodL, hpq, hn, hsc, hK', hmod, hgate, hAll⟩
  obtain ⟨φ₁, φ₂, hL, hk₁, hK, hk₂, hJ, hc, hdiag⟩ := hCD G p B Bs x L D J n f y' K' h'
  have hCtx := ggFarCtx_of_cfg h' hL hk₁ hK hk₂ hc hdiag
  exact ggTypeANbr_generated hCtx (by rw [← hc]; exact hJ) hK

end CFSG.StandardType

end
