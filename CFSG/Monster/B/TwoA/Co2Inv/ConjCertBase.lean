
module

public import CFSG.Monster.B.TwoA.Co2Inv.RowsBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

theorem rowOf_encL : ∀ (l : List ℕ) (t : ℕ), rowOf (encL l) t = l.getD t 0 % 2 ^ 22
  | [], t => by simp [rowOf, encL]
  | r :: l, 0 => by
    simp only [rowOf, encL, mul_zero, pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | r :: l, t + 1 => by
    rw [List.getD_cons_succ, ← rowOf_encL l t, rowOf, rowOf, encL]
    congr 1
    rw [show 22 * (t + 1) = 22 + 22 * t by ring, pow_add, ← Nat.div_div_eq_div_mul]
    congr 1
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)),
      zero_add]

theorem rowOf_lt (n t : ℕ) : rowOf n t < 2 ^ 22 := Nat.mod_lt _ (by positivity)

theorem rowsOf_getElem (n : ℕ) {t : ℕ} (ht : t < 22) : (rowsOf n)[t]! = rowOf n t := by
  rw [rowsOf, getElem!_pos _ _ (by simp [ht])]
  simp

theorem decW_mod (c : ℕ) : decW (c % 2 ^ 22) = decW c := by
  unfold decW
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [bvec_apply, bvec_apply, Nat.testBit_mod_two_pow, decide_eq_true t.2, Bool.true_and]

theorem rowsEnd_congr_decW {A B : Array ℕ} (h : ∀ t < 22, decW A[t]! = decW B[t]!) :
    rowsEnd A = rowsEnd B :=
  eq_rowsEnd_of fun t => by rw [rowsEnd_qbW, h t t.2]

def decE (n : ℕ) : Module.End (ZMod 2) (Wv v0) := rowsEnd (rowsOf n)

theorem gRows_eq (k : Fin 24) : gRows k = genQuotMatrix k := rfl

theorem idRows_getElem {t : ℕ} (ht : t < 22) : idRows[t]! = 1 <<< t := by
  rw [idRows, getElem!_pos _ _ (by simp [ht])]
  simp

@[instance_reducible] def conjEndAction :
    MulAction (Kstab v0) (Module.End (ZMod 2) (Wv v0)) where
  smul g T := wAct v0 g⁻¹ * T * wAct v0 g
  one_smul T := by
    change wAct v0 1⁻¹ * T * wAct v0 1 = T
    rw [inv_one, wAct_one, one_mul, mul_one]
  mul_smul g h T := by
    change wAct v0 (g * h)⁻¹ * T * wAct v0 (g * h) =
      wAct v0 g⁻¹ * (wAct v0 h⁻¹ * T * wAct v0 h) * wAct v0 g
    rw [mul_inv_rev, wAct_mul, wAct_mul]
    simp only [mul_assoc]

attribute [local instance] conjEndAction

theorem smul_end_def (g : Kstab v0) (T : Module.End (ZMod 2) (Wv v0)) :
    g • T = wAct v0 g⁻¹ * T * wAct v0 g := rfl

theorem smul_wAct (g x : Kstab v0) : g • wAct v0 x = wAct v0 (g * x * g⁻¹) := by
  rw [smul_end_def, wAct_mul, wAct_mul, mul_assoc]

theorem decE_injective {a b : ℕ} (ha : validConj a = true) (hb : validConj b = true)
    (h : decE a = decE b) : a = b := by
  have hrow : ∀ t < 22, rowOf a t = rowOf b t := by
    intro t ht
    have e := LinearMap.congr_fun h (qbW ⟨t, ht⟩)
    rw [decE, decE, rowsEnd_qbW, rowsEnd_qbW, rowsOf_getElem _ ht, rowsOf_getElem _ ht] at e
    exact decW_injective (rowOf_lt _ _) (rowOf_lt _ _) e
  have hrows : rowsOf a = rowsOf b := by
    rw [rowsOf, rowsOf]
    congr 1
    exact List.map_congr_left fun t ht => hrow t (List.mem_range.1 ht)
  rw [validConj, beq_iff_eq] at ha hb
  rw [ha, hb, hrows]

end CFSG.Monster.B.TwoA.Co2Inv
