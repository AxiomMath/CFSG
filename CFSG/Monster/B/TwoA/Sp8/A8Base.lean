
module

public import CFSG.Monster.B.TwoA.Sp8.LiftsBase
public import CFSG.Monster.Visible.SignCompat.Triality
public meta import CFSG.Monster.B.Rep4371.Model
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.B.Co2

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

def slPair : Pvis := signLiftPair ⟨dC, 0⟩

theorem slPair_eq : slPair = ⟨(YU ⟨toC 3, 0⟩, gO (toC 3)), YU_gO_mem_Pvis _⟩ := by
  apply Subtype.ext
  rw [slPair, coe_signLiftPair, dC_eq_toC]

theorem conjQ_slPair_pauliQ (y : Model.Pauli) :
    conjQ slPair (pauliQ y) = pauliQ (Model.conjYN 3 y) := by
  rw [slPair_eq]
  exact conjQ_sign_toQ 3 y

theorem pvis_comm_of_conj {p x : Pvis} (h : p⁻¹ * x * p = x) : x * p = p * x := by
  calc x * p = p * (p⁻¹ * x * p) := by group
    _ = p * x := by rw [h]

theorem thetaEquiv_comm_rhoEquiv {p : Pvis} {r : Q} (h : conjQ p r = r) :
    thetaEquiv p * rhoEquiv r = rhoEquiv r * thetaEquiv p := by
  have h1 := Census.inv_mul_rhoPair_mul p r
  rw [h] at h1
  have h2 := pvis_comm_of_conj h1
  show thetaEquiv p * thetaEquiv (rhoPair r) = thetaEquiv (rhoPair r) * thetaEquiv p
  rw [← thetaEquiv_mul, ← thetaEquiv_mul]
  exact congrArg thetaEquiv h2

theorem thetaEquiv_slPair : thetaEquiv slPair = tauB * rhoEquiv (XQ ⟨dC, 0⟩) * tauB⁻¹ :=
  thetaEquiv_signLiftPair _

end CFSG.Monster.B.TwoA.Sp8
