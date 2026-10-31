
module

public import CFSG.Monster.B.TwoA.Sp8.DataBase
public import CFSG.Monster.B.TwoA.Census.CentralSqrt
public meta import CFSG.Monster.B.Rep4371.Model
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census

def PhiQ (v : Fin 8 → ZMod 2) : Q := pauliQ (foldP v)

theorem pauliQ_injective_box {x y : Model.Pauli} (hx : x.2.1 < 2 ^ 12 ∧ x.2.2 < 2 ^ 12)
    (hy : y.2.1 < 2 ^ 12 ∧ y.2.2 < 2 ^ 12) (h : pauliQ x = pauliQ y) : x = y := by
  have h1 := spinEquiv.injective h
  have hs := congrArg SpinCoord.s h1
  have ha := congrArg SpinCoord.a h1
  have hd := congrArg SpinCoord.δ h1
  simp only [toSC_s, toSC_a, toSC_δ] at hs ha hd
  obtain ⟨xs, xa, xd⟩ := x
  obtain ⟨ys, ya, yd⟩ := y
  simp only [pauli_s, pauli_a, pauli_d] at hs ha hd
  simp only at hx hy
  have h1 := boolZ_injective hs
  have h2 := toC_injective hx.1 hy.1 ha
  have h3 := toD_injective hx.2 hy.2 hd
  rw [h1, h2, h3]

theorem kappa_congr {q q' : Q} (h : q = q') (hq : rhoEquiv q ∈ Cgen) (hq' : rhoEquiv q' ∈ Cgen) :
    kappa ⟨rhoEquiv q, hq⟩ = kappa ⟨rhoEquiv q', hq'⟩ := by
  subst h
  rfl

theorem pauliQ_z : pauliQ (true, 0, 0) = zQ := by
  rw [pauliQ, zQ]
  congr 1
  refine SpinCoord.ext rfl ?_ ?_
  · rw [toSC_a, pauli_a, toC_zero]
    rfl
  · rw [toSC_δ, pauli_d, toD_zero]
    rfl

theorem pauliQ_omega : pauliQ (false, 63, 0) = wQ := by
  rw [pauliQ, wQ, XQ_eq]
  congr 1
  refine SpinCoord.ext rfl ?_ ?_
  · rw [toSC_a, pauli_a, ← ΩC_eq_toC]
  · rw [toSC_δ, pauli_d, ΩC_eq_toC, thetaD_toC]
    rfl

theorem toD_deltaPair {i j : Fin 24} {w D : ℕ} (hb : bvec 24 w = Pi.single i 1 + Pi.single j 1)
    (h : Model.dualN w = D) : deltaPair i j = toD D := by
  rw [← h, ← mk_bvec_eq_toD, deltaPair, hb]

theorem pauliQ_cocode {i j : Fin 24} {w D : ℕ} (hb : bvec 24 w = Pi.single i 1 + Pi.single j 1)
    (h : Model.dualN w = D) : pauliQ (false, 0, D) = rMinus i j := by
  rw [pauliQ, rMinus, DQ_eq, toD_deltaPair hb h]
  congr 1
  refine SpinCoord.ext rfl ?_ rfl
  rw [toSC_a, pauli_a, toC_zero]

theorem dC_eq_toC : dC = toC 3 := by
  apply Subtype.ext
  rw [coe_toC]
  decide +kernel

theorem pauliQ_X : pauliQ (false, 3, 60) = XQ ⟨dC, 0⟩ := by
  rw [pauliQ, XQ_eq]
  congr 1
  refine SpinCoord.ext rfl ?_ ?_
  · rw [toSC_a, pauli_a, dC_eq_toC]
  · rw [toSC_δ, pauli_d, dC_eq_toC, thetaD_toC]
    rfl

end CFSG.Monster.B.TwoA.Sp8
