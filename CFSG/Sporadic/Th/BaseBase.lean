
module

public import CFSG.Sporadic.Th.PlaneBase
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public meta import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.OrbitSpec
public import CFSG.Sporadic.Th.SetupBase

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Matrix Pointwise

def bz (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bz_xor (x y : Bool) : bz (x ^^ y) = bz x + bz y := by
  cases x <;> cases y <;> decide

theorem foldl_xor_eq_sum (p : ℕ → Bool) (n : ℕ) :
    bz ((List.range n).foldl (fun acc j => acc ^^ p j) false) =
      ∑ j ∈ Finset.range n, bz (p j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil, bz_xor]

theorem dot_spec (u w : V4) : bz (u.dot w) = u.toVec ⬝ᵥ w.toVec := by
  rw [V4.dot, foldl_xor_eq_sum, dotProduct,
    ← Fin.sum_univ_eq_sum_range (fun j => bz (u.testBit j && w.testBit j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [V4.toVec_apply, bz]
  cases u.testBit j.val <;> cases w.testBit j.val <;> simp

def keyVec (k : Key) (a : Fin 2) : Fin 248 → ZMod 2 :=
  if a = 0 then k.u.toVec else k.v.toVec

theorem keyVec_zero (k : Key) : keyVec k 0 = k.u.toVec := rfl

theorem keyVec_one (k : Key) : keyVec k 1 = k.v.toVec := rfl

theorem gramCode_eq_of (K : Fin 2 → Fin 2 → ZMod 2) (b00 b01 b10 b11 : Bool)
    (h00 : K 0 0 = bz b00) (h01 : K 0 1 = bz b01) (h10 : K 1 0 = bz b10) (h11 : K 1 1 = bz b11) :
    gramCode K = bitN b00 + 2 * bitN b01 + 4 * bitN b10 + 8 * bitN b11 := by
  rw [gramCode, h00, h01, h10, h11]
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> rfl

theorem gramCodeN_formT (ki kj : Key) :
    gramCodeN (formT ()) ki kj =
      gramCode (fun a b => keyVec ki a ⬝ᵥ (formF *ᵥ keyVec kj b)) := by
  have hF (v : V4) : (frApply (formT ()) v).toVec = formF *ᵥ v.toVec :=
    frApply_transposeRows_toVec fcRows v
  rw [gramCodeN, gramCode_eq_of _ (ki.u.dot (frApply (formT ()) kj.u))
    (ki.u.dot (frApply (formT ()) kj.v)) (ki.v.dot (frApply (formT ()) kj.u))
    (ki.v.dot (frApply (formT ()) kj.v))]
  · simp only [dot_spec, hF, keyVec_zero]
  · simp only [dot_spec, hF, keyVec_zero, keyVec_one]
  · simp only [dot_spec, hF, keyVec_zero, keyVec_one]
  · simp only [dot_spec, hF, keyVec_one]

theorem cRows_size : cRows.size = 248 := by simp [cRows]

theorem cRows_getD (k : Fin 248) :
    (cRows[k.val]?.getD V4.zero).toVec = keyVec (deltaKeys[k.val / 2]!) ⟨k.val % 2,
      Nat.mod_lt _ two_pos⟩ := by
  have hk : k.val < cRows.size := by rw [cRows_size]; exact k.isLt
  rw [Array.getElem?_eq_getElem hk, Option.getD_some]
  simp only [cRows, Array.getElem_ofFn]
  rcases Nat.mod_two_eq_zero_or_one k.val with h | h
  · simp [h, keyVec]
  · simp [h, keyVec]

end CFSG.Sporadic.Th
