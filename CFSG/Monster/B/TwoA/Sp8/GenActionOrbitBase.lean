
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitInputs
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.Rep4371.SmallFaithfulBase
public import CFSG.Monster.B.Gen.Max2AssemblyBase
public import CFSG.Monster.B.Gen.PacketGenerationBase
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Co2
  CFSG.Monster.B.TwoA.Census

theorem bvec8_injective {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : bvec 8 a = bvec 8 b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have h1 := congrFun h ⟨i, hi⟩
    simp only [bvec_apply] at h1
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · have h256 : 256 ≤ 2 ^ i := by
      calc (256 : ℕ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem bvec8_one : bvec 8 1 = (Pi.single 0 1 : V8) := by decide

theorem bvec8_two_pow : ∀ t : Fin 8, bvec 8 (2 ^ (t : ℕ)) = (Pi.single t 1 : V8) := by decide

theorem bvec8_mod (x : ℕ) : bvec 8 (x % 2 ^ 22) = bvec 8 x := by
  funext t
  rw [bvec_apply, bvec_apply, Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and]

@[expose] def tupDec (n : ℕ) : Fin 8 → V8 := fun t => bvec 8 (Co2Inv.rowOf n t)

theorem getD_range_map (f : ℕ → ℕ) {t : ℕ} (ht : t < 8) :
    ((List.range 8).map f).getD t 0 = f t := by
  rw [List.getD_eq_getElem _ _ (by simp [ht])]
  simp

theorem tupValid_spec {n : ℕ} (h : tupValid n = true) :
    n = Co2Inv.encL ((List.range 8).map (Co2Inv.rowOf n)) ∧ ∀ t < 8, Co2Inv.rowOf n t < 256 := by
  simp only [tupValid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact h

theorem tupDec_injective (a b : ℕ) (ha : tupValid a = true) (hb : tupValid b = true)
    (h : tupDec a = tupDec b) : a = b := by
  obtain ⟨ea, ra⟩ := tupValid_spec ha
  obtain ⟨eb, rb⟩ := tupValid_spec hb
  have hrow : ∀ t < 8, Co2Inv.rowOf a t = Co2Inv.rowOf b t := fun t ht =>
    bvec8_injective (ra t ht) (rb t ht) (congrFun h ⟨t, ht⟩)
  rw [ea, eb]
  congr 1
  exact List.map_congr_left fun t ht => hrow t (List.mem_range.1 ht)

theorem tupDec_root : tupDec tupRoot = fun t => (Pi.single t 1 : V8) := by
  funext t
  rw [tupDec, tupRoot, Co2Inv.rowOf_encL, bvec8_mod, getD_range_map _ t.2, bvec8_two_pow]

end CFSG.Monster.B.TwoA.Sp8
