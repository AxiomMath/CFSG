
module

public import CFSG.Monster.B.TwoA.Unitary.SemilinearBase
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.PlanesBase
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsInputs
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.BData
public import CFSG.Monster.B.TwoA.Unitary.PlanesInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer
open CFSG.Monster.B.Classical.UnitarySix (bar)

@[expose] def IsSingPt (P : Submodule F4 V6) : Prop :=
  Module.finrank F4 P = 1 ∧ ∀ s ∈ P, ∀ t ∈ P, hU s t = 0

@[expose] def singPt (i : Fin 693) : Submodule F4 V6 := Submodule.span F4 {singVec i}

theorem hU_smul_smul (a b : F4) (v : V6) : hU (a • v) (b • v) = a * bar b * hU v v := by
  rw [hU_smul_left, hU_smul_right, mul_assoc]

theorem isSingPt_span {v : V6} (hv : v ≠ 0) (hvv : hU v v = 0) :
    IsSingPt (Submodule.span F4 {v}) := by
  refine ⟨finrank_span_singleton hv, fun s hs t ht => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hs
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 ht
  rw [hU_smul_smul, hvv, mul_zero]

@[expose] def singGen (k : Fin 17) (i : Fin 693) : Fin 693 := singLook (b6Map k (singVec i))

@[expose] def PermutesS (x : SigmaU6) : Prop := ∀ i, ∃ i', sigmaAct (singPt i) x = singPt i'

theorem PermutesS.mul {x y : SigmaU6} (hx : PermutesS x) (hy : PermutesS y) :
    PermutesS (x * y) := by
  intro i
  obtain ⟨i', hi'⟩ := hx i
  obtain ⟨i'', hi''⟩ := hy i'
  exact ⟨i'', by rw [sigmaAct_mul, hi', hi'']⟩

end CFSG.Monster.B.TwoA.Unitary
