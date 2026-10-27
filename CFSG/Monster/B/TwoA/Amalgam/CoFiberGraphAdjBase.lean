
module

public import CFSG.Monster.B.TwoA.Base.PsiV
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Monster.B.TwoA.Sp8.SubgeomCard
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Base
public import CFSG.Monster.B.TwoA.Unitary.TwentyBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0 wAct_mul wAct_one wAct_inv_apply wAct_apply_inv decW)

theorem bV_sigmaW_tauW :
    bV Unitary.sigmaW Unitary.tauW = 1 := by
  rw [show Unitary.tauW = decW 60 from rfl]
  exact (Unitary.bW_sigmaW_decW 60).trans (by decide +kernel)

theorem bV_sigmaW_of_mem_tauOrb
    {x : Wv v0} (hx : x ∈ Unitary.usigOrbit Unitary.tauW) :
    bV Unitary.sigmaW x = 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  have h := Unitary.bW_wAct u Unitary.sigmaW Unitary.tauW
  rw [Unitary.mem_Usig.1 hu] at h
  exact h.trans bV_sigmaW_tauW

theorem omegaGraph_adj_smul
    (g : Kstab v0) (α β : Unitary.OmegaPt) :
    Unitary.omegaGraph.Adj (g • α) (g • β) ↔ Unitary.omegaGraph.Adj α β := by
  simp only [Unitary.omegaGraph, CFSG.Monster.B.Generic.suborbitGraph_adj,
    CFSG.Monster.B.Generic.card_orbit_stabilizer_smul, ne_eq, smul_left_cancel_iff]

end CFSG.Monster.B.TwoA.Amalgam
