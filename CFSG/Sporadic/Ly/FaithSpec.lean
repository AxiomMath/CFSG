module

public import CFSG.Sporadic.Ly.KeySpec
public import Certificates.Data.CFSGNative.Ly.Faith

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Ly

open Native Matrix Finset
open CFSG.Sporadic.He.Native (toMat toVec toMat_mulM toVec_mulVec toMat_idM toMat_eq_of_beq
  toVec_eq_of_beq toMat_colsMat getElem!_ofFn fold_add_eq_sum mulM mulVec idM colsMat)

theorem toMat_transM (X : Array (Array ℕ)) : toMat 5 111 (transM X) = (toMat 5 111 X)ᵀ := by
  ext i j
  simp only [toMat, of_apply, transpose_apply]
  unfold transM
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt]

theorem fold7_eq (f : ℕ → ℕ) :
    ((Nat.fold 7 (fun l _ acc => acc + f l) 0 : ℕ) : ZMod 5) = ∑ l : Fin 7, (f l.val : ZMod 5) := by
  rw [fold_add_eq_sum, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun l => (f l : ZMod 5)) 7]

theorem toMat_keyTensor (key : ByteArray) : toMat 5 111 (keyTensor key) = keyT key := by
  ext i j
  simp only [toMat, of_apply, keyT, mul_apply, transpose_apply, keyU, keyC]
  unfold keyTensor
  simp only
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt, ZMod.natCast_mod, fold7_eq]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ b.isLt, getElem!_ofFn _ j.isLt,
    getElem!_ofFn _ b.isLt, Nat.cast_mul, ZMod.natCast_mod, fold7_eq, Finset.sum_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ a.isLt, getElem!_ofFn _ a.isLt,
    getElem!_ofFn _ b.isLt]
  push_cast
  ring

theorem arr_getElem!_push_lt {α : Type*} [Inhabited α] (xs : Array α) (x : α) {i : ℕ}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by simp; omega), getElem!_pos xs i h, Array.getElem_push_lt h]

theorem arr_getElem!_push_eq {α : Type*} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos (xs.push x) xs.size (by simp), Array.getElem_push_eq]

theorem cyclicVecs_spec (Z : Array (Array (Array ℕ))) (v : Array ℕ) (par op : Array ℕ)
    (hpar : ∀ t < 110, par[t]! ≤ t) : ∀ n ≤ 110,
    (Nat.fold n (fun t _ cs => cs.push (mulVec 5 111 Z[op[t]!]! cs[par[t]!]!)) #[v]).size =
      n + 1 ∧
    (Nat.fold n (fun t _ cs => cs.push (mulVec 5 111 Z[op[t]!]! cs[par[t]!]!)) #[v])[0]! = v ∧
    ∀ t < n, (Nat.fold n (fun t _ cs => cs.push (mulVec 5 111 Z[op[t]!]! cs[par[t]!]!))
        #[v])[t + 1]! = mulVec 5 111 Z[op[t]!]!
          (Nat.fold n (fun t _ cs => cs.push (mulVec 5 111 Z[op[t]!]! cs[par[t]!]!))
            #[v])[par[t]!]! := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨by simp, by simp, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨hs, h0, ht⟩ := ih (by omega)
    rw [Nat.fold_succ]
    set cs := Nat.fold n (fun t _ cs => cs.push (mulVec 5 111 Z[op[t]!]! cs[par[t]!]!)) #[v]
    refine ⟨by rw [Array.size_push, hs], ?_, fun t htn => ?_⟩
    · rw [arr_getElem!_push_lt _ _ (by rw [hs]; omega)]; exact h0
    · have hp := hpar t (by omega)
      by_cases htn' : t < n
      · rw [arr_getElem!_push_lt _ _ (by rw [hs]; omega), ht t htn',
          arr_getElem!_push_lt _ _ (by rw [hs]; omega)]
      · have e : t = n := by omega
        rw [e] at hp ⊢
        rw [show n + 1 = cs.size by rw [hs], arr_getElem!_push_eq,
          arr_getElem!_push_lt _ _ (by rw [hs]; omega)]

structure FaithFacts (qkeys : Array ByteArray) (F Y Cinv : Array (Array ℕ))
    (v w par op : Array ℕ) (ab : ℕ × ℕ) (mu : ℕ) : Prop where
  qsize : qkeys.size = 16
  ha : ab.1 < 16
  hb : ab.2 < 16
  vsize : v.size = 111
  par_le : ∀ t < 110, par[t]! ≤ t
  op_lt : ∀ t < 110, op[t]! < 16
  hNv : mulVec 5 111 (faithN (faithZ qkeys F) ab mu) v = Array.replicate 111 0
  hYN : mulM 5 111 Y (faithN (faithZ qkeys F) ab mu) = faithP v w
  hC : mulM 5 111 (colsMat 111 (cyclicVecs (faithZ qkeys F) v par op)) Cinv = idM 111

theorem faithChecks_facts {qkeys : Array ByteArray} {F Y Cinv : Array (Array ℕ)}
    {v w par op : Array ℕ} {ab : ℕ × ℕ} {mu : ℕ}
    (h : faithChecks qkeys F Y Cinv v w par op ab mu = true) :
    FaithFacts qkeys F Y Cinv v w par op ab mu := by
  unfold faithChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, fun t ht => ?_, fun t ht => (h8 t ht).2, h9, h10, h11⟩
  have := (h8 t ht).1
  omega

theorem faithZ_get {qkeys : Array ByteArray} {F : Array (Array ℕ)} {h : ℕ} (hh : h < qkeys.size) :
    toMat 5 111 (faithZ qkeys F)[h]! = keyT qkeys[h]! * toMat 5 111 F := by
  unfold faithZ
  rw [getElem!_pos _ h (by simpa using hh), Array.getElem_map, toMat_mulM, toMat_keyTensor,
    getElem!_pos qkeys h hh]

theorem toMat_faithN (Z : Array (Array (Array ℕ))) (ab : ℕ × ℕ) (mu : ℕ) :
    toMat 5 111 (faithN Z ab mu) =
      toMat 5 111 Z[ab.1]! * toMat 5 111 Z[ab.2]! - (mu : ZMod 5) • 1 := by
  ext i j
  rw [← toMat_mulM]
  simp only [toMat, of_apply, Matrix.sub_apply, Matrix.smul_apply, one_apply, smul_eq_mul]
  unfold faithN
  simp only
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt, ZMod.natCast_mod, Nat.cast_add]
  by_cases e : i = j
  · subst e
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_one, Nat.cast_sub (by omega), ZMod.natCast_self,
      zero_sub, ← sub_eq_add_neg, ZMod.natCast_mod]
  · rw [ite_eq_right (fun h => e (Fin.ext h)), ite_eq_right e, mul_zero, sub_zero, Nat.cast_zero,
      add_zero]

theorem toMat_faithP (v w : Array ℕ) :
    toMat 5 111 (faithP v w) = 1 - Matrix.vecMulVec (toVec 5 111 v) (toVec 5 111 w) := by
  ext i j
  simp only [toMat, of_apply, Matrix.sub_apply, one_apply, vecMulVec_apply, toVec]
  unfold faithP
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_mul, Nat.cast_mul]
  have h4 : ((4 : ℕ) : ZMod 5) = -1 := by decide
  rw [h4]
  by_cases e : i = j
  · subst e
    rw [ite_eq_left rfl, ite_eq_left rfl, Nat.cast_one]
    ring
  · rw [ite_eq_right (fun h => e (Fin.ext h)), ite_eq_right e, Nat.cast_zero]
    ring

theorem scalar_of_commute {qkeys : Array ByteArray} {F Y Cinv : Array (Array ℕ)}
    {v w par op : Array ℕ} {ab : ℕ × ℕ} {mu : ℕ} (hF : FaithFacts qkeys F Y Cinv v w par op ab mu)
    (T : Matrix (Fin 111) (Fin 111) (ZMod 5))
    (hT : ∀ h < 16, T * (keyT qkeys[h]! * toMat 5 111 F) = keyT qkeys[h]! * toMat 5 111 F * T) :
    ∃ c : ZMod 5, T = c • 1 := by
  set Z := faithZ qkeys F with hZ
  have hZc : ∀ h < 16, T * toMat 5 111 Z[h]! = toMat 5 111 Z[h]! * T := by
    intro h hh
    rw [hZ, faithZ_get (by rw [hF.qsize]; exact hh)]
    exact hT h hh
  set Za := toMat 5 111 Z[ab.1]! with hZa
  set Zb := toMat 5 111 Z[ab.2]! with hZb
  set N := toMat 5 111 (faithN Z ab mu) with hN
  have hTN : T * N = N * T := by
    have ha : T * Za = Za * T := hZc _ hF.ha
    have hb : T * Zb = Zb * T := hZc _ hF.hb
    rw [hN, toMat_faithN, ← hZa, ← hZb]
    calc T * (Za * Zb - (mu : ZMod 5) • 1) = (T * Za) * Zb - (mu : ZMod 5) • T := by
          rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
      _ = Za * (T * Zb) - (mu : ZMod 5) • T := by rw [ha, Matrix.mul_assoc]
      _ = (Za * Zb - (mu : ZMod 5) • 1) * T := by
          rw [hb, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
  set vv := toVec 5 111 v with hvv
  set ww := toVec 5 111 w with hww
  have hNv : N *ᵥ vv = 0 := by
    have := toVec_eq_of_beq (p := 5) (d := 111) (beq_iff_eq.2 hF.hNv)
    rw [toVec_mulVec] at this
    rw [hN, hvv, this]
    funext i
    simp only [toVec, Pi.zero_apply]
    rw [getElem!_pos _ i.val (by simp), Array.getElem_replicate]
    exact Nat.cast_zero
  have hYN : toMat 5 111 Y * N = 1 - Matrix.vecMulVec vv ww := by
    rw [hN, ← toMat_mulM, hF.hYN, toMat_faithP]
  set x := T *ᵥ vv with hx
  have hNx : N *ᵥ x = 0 := by
    rw [hx, Matrix.mulVec_mulVec, ← hTN, ← Matrix.mulVec_mulVec, hNv, Matrix.mulVec_zero]
  have hPx : (1 - Matrix.vecMulVec vv ww) *ᵥ x = 0 := by
    rw [← hYN, ← Matrix.mulVec_mulVec, hNx, Matrix.mulVec_zero]
  set c := ww ⬝ᵥ x with hc
  have hTv : x = c • vv := by
    have hP : x - Matrix.vecMulVec vv ww *ᵥ x = 0 := by
      rw [← hPx, Matrix.sub_mulVec, Matrix.one_mulVec]
    have hvx : Matrix.vecMulVec vv ww *ᵥ x = c • vv := by
      funext i
      simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hc]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hvx] at hP
    exact sub_eq_zero.1 hP
  set cs := cyclicVecs Z v par op with hcs
  have hspec := cyclicVecs_spec Z v par op hF.par_le 110 le_rfl
  have hcs_eq : cs = Nat.fold 110 (fun t _ cs => cs.push (mulVec 5 111 Z[op[t]!]! cs[par[t]!]!))
      #[v] := rfl
  have hall : ∀ j ≤ 110, T *ᵥ toVec 5 111 cs[j]! = c • toVec 5 111 cs[j]! := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · rw [hcs_eq, hspec.2.1]; exact hTv
      · obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
        have ht : t < 110 := by omega
        rw [hcs_eq, hspec.2.2 t ht, ← hcs_eq, toVec_mulVec, Matrix.mulVec_mulVec,
          hZc _ (hF.op_lt t ht), ← Matrix.mulVec_mulVec,
          ih _ (by have := hF.par_le t ht; omega) (by have := hF.par_le t ht; omega),
          Matrix.mulVec_smul]
  set C := toMat 5 111 (colsMat 111 cs) with hC
  have hTC : T * C = c • C := by
    ext i t
    have := congrFun (hall t.val (by omega)) i
    rw [Matrix.mul_apply, Matrix.smul_apply, hC, toMat_colsMat]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [toMat_colsMat]
  have hCinv : C * toMat 5 111 Cinv = 1 := by
    rw [hC, ← toMat_mulM, hF.hC, toMat_idM]
  refine ⟨c, ?_⟩
  calc T = T * (C * toMat 5 111 Cinv) := by rw [hCinv, Matrix.mul_one]
    _ = (T * C) * toMat 5 111 Cinv := by rw [Matrix.mul_assoc]
    _ = c • 1 := by rw [hTC, Matrix.smul_mul, hCinv]

end CFSG.Sporadic.Ly
