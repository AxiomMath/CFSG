
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffBase
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionDiffBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
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

theorem conj_iotaD_kappa {g x : Cgen} : iotaD (kappa g) * iotaD (kappa x) * (iotaD (kappa g))⁻¹ =
    iotaD (kappa (g * x * g⁻¹)) := by
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]

theorem bvec_seven_eq_zero {r : ℕ} (hr : r < 128) : bvec 8 r 7 = 0 := by
  have h : r.testBit 7 = false := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp only [decide_eq_false_iff_not]
    omega
  show (if r.testBit 7 then 1 else 0 : ZMod 2) = 0
  rw [h]
  rfl

theorem bvec_seven_eq_one {r : ℕ} (h1 : 128 ≤ r) (h2 : r < 256) : bvec 8 r 7 = 1 := by
  have h : r.testBit 7 = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp only [decide_eq_true_eq]
    omega
  show (if r.testBit 7 then 1 else 0 : ZMod 2) = 1
  rw [h]
  rfl

theorem genRow_tri : ∀ j : Fin 8, genRow 44 j = triRows.getD j 0 := by decide

end CFSG.Monster.B.TwoA.Sp8
