
module

public import CFSG.Monster.Visible.SignCompat.TrialityCycle
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.Griess
open CFSG.Monster.B.TwoA.Co2Inv (dC)

theorem P_dC : P ((dC : C) : Fin 24 → ZMod 2) = 0 := by
  decide +kernel

theorem tauB_conj_slPair :
    tauB * thetaEquiv (signLiftPair ⟨dC, 0⟩) * tauB⁻¹ =
      thetaEquiv (signLiftPair ⟨dC, 0⟩) * rhoEquiv (XQ ⟨dC, 0⟩) :=
  tauB_conj_thetaEquiv_signLiftPair _ P_dC

theorem tauB_conj_slPair_eq :
    tauB * thetaEquiv (signLiftPair ⟨dC, 0⟩) * tauB⁻¹ =
      thetaEquiv (rhoPair (XQ ⟨dC, 0⟩) * signLiftPair ⟨dC, 0⟩) :=
  tauB_conj_thetaEquiv_signLiftPair_eq _ P_dC

end CFSG.Monster.Visible
