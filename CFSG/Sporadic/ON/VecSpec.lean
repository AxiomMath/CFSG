module

public import Certificates.Data.CFSGNative.ON.Basic
public import CFSG.Sporadic.Fi23.WideSpec

public section

namespace CFSG.Sporadic.ON.Native

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native Matrix

@[expose] def vecOf (a : W) : Fin 154 → ZMod 3 := fun j => a.toV.val j.val

theorem vecOf_apply (a : W) (j : Fin 154) : vecOf a j = a.toV.val j.val := rfl

private theorem testBit_of_shr26 {x : UInt64} (h : x >>> 26 = 0) {t : ℕ} (ht : 26 ≤ t) :
    x.toNat.testBit t = false := by
  have e := congrArg (fun y : UInt64 => y.toNat.testBit (t - 26)) h
  simp only [UInt64.toNat_shiftRight, Nat.testBit_shiftRight, UInt64.toNat_zero,
    Nat.zero_testBit] at e
  have h26 : (26 : UInt64).toNat % 64 = 26 := by decide
  rwa [h26, show 26 + (t - 26) = t by omega] at e

private theorem join_shr_154 {x0 x1 x2 x3 : UInt64} (h2 : x2 >>> 26 = 0) (h3 : x3 = 0) :
    join x0 x1 x2 x3 >>> 154 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.zero_testBit, testBit_join]
  unfold limb
  by_cases hq : (154 + i) / 64 = 2
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hq]
    exact testBit_of_shr26 h2 (by omega)
  · by_cases hq3 : (154 + i) / 64 = 3
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hq, ite_eq_left hq3, h3]
      simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hq, ite_eq_right hq3]
      simp

theorem canon154_spec {a : W} (h : canon154 a = true) :
    (a.toV.wf && a.toV.p >>> 154 == 0 && a.toV.m >>> 154 == 0) = true := by
  unfold canon154 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨⟨⟨⟨hw, hp2⟩, hm2⟩, hp3⟩, hm3⟩ := h
  exact ⟨⟨W.wf_spec hw, join_shr_154 hp2 hp3⟩, join_shr_154 hm2 hm3⟩

theorem wf_of_canon154 {a : W} (h : canon154 a = true) : a.toV.wf = true := by
  have := canon154_spec h
  simp only [Bool.and_eq_true] at this
  exact this.1.1

theorem vecOf_inj {a b : W} (ha : canon154 a = true) (hb : canon154 b = true)
    (h : vecOf a = vecOf b) : a = b := by
  apply W.toV_inj
  apply V.eq_of_canon (canon154_spec ha) (canon154_spec hb)
  intro j hj
  exact congrFun h ⟨j, hj⟩

theorem vecOf_neg {a : W} (h : a.toV.wf = true) : vecOf a.neg = -vecOf a := by
  funext j
  rw [vecOf_apply, W.toV_neg, V.val_neg _ _ h, Pi.neg_apply, vecOf_apply]

theorem wf_combW {Y : Array W} (hY : RowsWF (toVM Y)) {r : W} (hr : r.toV.wf = true) :
    (combW 154 Y r).toV.wf = true := by
  rw [toV_combW]
  exact V.wf_comb 154 _ _ hY hr

theorem vecOf_combW {Y : Array W} (hY : RowsWF (toVM Y)) {r : W} (hr : r.toV.wf = true) :
    vecOf (combW 154 Y r) = ∑ j : Fin 154, vecOf r j • vecOf Y[j.val]! := by
  funext k
  rw [vecOf_apply, toV_combW, V.val_comb 154 _ _ hY hr, Finset.sum_apply,
    Finset.sum_range (fun j => r.toV.val j * (toVM Y)[j]!.val k.val)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toVM_getElem!, Pi.smul_apply, smul_eq_mul]
  rfl

theorem toVM_transpose_map_ofV (X : Array V) :
    toVM ((F3.Native.transpose 154 X).map ofV) = F3.Native.transpose 154 X := by
  apply toVM_map_ofV
  intro v hv
  unfold F3.Native.transpose at hv
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
  rw [Array.getElem_ofFn]
  obtain ⟨h1, h2⟩ := V.ofFn_lt 154 (fun i' => X[i']!.get i)
  exact ⟨lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by norm_num)),
    lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by norm_num))⟩

theorem vecOf_mulVecT (X : Array V) {r : W} (hr : r.toV.wf = true) :
    vecOf (mulVecT ((F3.Native.transpose 154 X).map ofV) r) = toMat 154 X *ᵥ vecOf r := by
  have hY : RowsWF (toVM ((F3.Native.transpose 154 X).map ofV)) := by
    rw [toVM_transpose_map_ofV]; exact RowsWF.transpose 154 X
  unfold mulVecT
  rw [vecOf_combW hY hr]
  funext k
  rw [Finset.sum_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  congr 1
  have e := congrFun (congrFun (toMat_transpose (d := 154) X) j) k
  rw [toMat_apply, Matrix.transpose_apply] at e
  rw [vecOf_apply, ← toVM_getElem!, toVM_transpose_map_ofV, e]

variable {K : Type*} [Field K] {d : Type*} [Fintype d] [DecidableEq d]

theorem eq_zero_of_vecMul_eq_zero {U X : Matrix d d K} (hXU : X * U = 1) {x : d → K}
    (h : x ᵥ* U = 0) : x = 0 := by
  have hUX : U * X = 1 := mul_eq_one_comm.1 hXU
  calc x = x ᵥ* (U * X) := by rw [hUX, Matrix.vecMul_one]
    _ = (x ᵥ* U) ᵥ* X := (Matrix.vecMul_vecMul x U X).symm
    _ = 0 := by rw [h, Matrix.zero_vecMul]

theorem eq_smul_one_of_rows {U X M : Matrix d d K} (hXU : X * U = 1) (μ : K)
    (h : ∀ t, M *ᵥ U t = μ • U t) : M = μ • 1 := by
  have hUM : U * Mᵀ = μ • U := by
    ext t j
    have := congrFun (h t) j
    rw [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply, Matrix.smul_apply, ← Pi.smul_apply, ← this]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.transpose_apply, mul_comm]
  have hMT : Mᵀ = μ • 1 := by
    calc Mᵀ = X * U * Mᵀ := by rw [hXU, Matrix.one_mul]
      _ = X * (U * Mᵀ) := Matrix.mul_assoc _ _ _
      _ = μ • 1 := by rw [hUM, Matrix.mul_smul, hXU]
  rw [← Matrix.transpose_transpose M, hMT, Matrix.transpose_smul, Matrix.transpose_one]

end CFSG.Sporadic.ON.Native
