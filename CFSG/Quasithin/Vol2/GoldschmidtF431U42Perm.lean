module

public import CFSG.Quasithin.Recognition.CertPermList
public import Certificates.Data.U42F431Perm
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

abbrev P45 := Equiv.Perm (Fin 45)

@[expose] def chkPermL (l il : List ℕ) : Bool :=
  (List.range 45).all fun i =>
    il.getD (l.getD i 0) 0 == i && l.getD (il.getD i 0) 0 == i && l.getD i 0 < 45 &&
      il.getD i 0 < 45

@[expose] def mkPerm (l il : List ℕ) (h : chkPermL l il = true) : P45 where
  toFun i := ⟨l.getD i 0, by have := List.all_eq_true.1 h i (List.mem_range.2 i.2); simp_all⟩
  invFun i := ⟨il.getD i 0, by have := List.all_eq_true.1 h i (List.mem_range.2 i.2); simp_all⟩
  left_inv i := by
    have := List.all_eq_true.1 h i (List.mem_range.2 i.2)
    ext
    simp_all
  right_inv i := by
    have := List.all_eq_true.1 h i (List.mem_range.2 i.2)
    ext
    simp_all

theorem repL_mkPerm (l il : List ℕ) (h : chkPermL l il = true) (hl : l.length = 45) :
    RepL l (mkPerm l il h) := ⟨hl, fun _ => rfl⟩

theorem chkPermL_x : chkPermL xL xL = true := by decide +kernel

theorem chkPermL_y : chkPermL yL yiL = true := by decide +kernel

theorem chkPermL_yi : chkPermL yiL yL = true := by decide +kernel

@[expose] def x45 : P45 := mkPerm xL xL chkPermL_x

@[expose] def y45 : P45 := mkPerm yL yiL chkPermL_y

theorem repL_x : RepL xL x45 := repL_mkPerm _ _ _ (by decide +kernel)

theorem repL_y : RepL yL y45 := repL_mkPerm _ _ _ (by decide +kernel)

theorem x45_mul_self : x45 * x45 = 1 := by
  refine eq_of_repL (l := comp xL xL) (repL_mul repL_x repL_x) ?_
  have : comp xL xL = List.range 45 := by decide +kernel
  rw [this]
  exact repL_one 45

theorem repL_yi : RepL yiL y45⁻¹ := by
  have h : RepL yiL (mkPerm yiL yL chkPermL_yi) := repL_mkPerm _ _ _ (by decide +kernel)
  have e : mkPerm yiL yL chkPermL_yi = y45⁻¹ := by
    ext i
    have := List.all_eq_true.1 chkPermL_y i (List.mem_range.2 i.2)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    simp only [y45, mkPerm, Equiv.Perm.inv_def]
    rfl
  rwa [e] at h

@[expose] def gP (k : ℕ) : P45 := if k % 3 = 0 then x45 else if k % 3 = 1 then y45 else y45⁻¹

theorem repL_gP (k : ℕ) : RepL (genL k) (gP k) := by
  unfold genL gP
  split_ifs
  · exact repL_x
  · exact repL_y
  · exact repL_yi

@[expose] def wordP (w : List ℕ) : P45 := (w.map gP).prod

theorem repL_wordP (w : List ℕ) : RepL (evalW w) (wordP w) := by
  induction w with
  | nil => exact repL_one 45
  | cons k w ih => exact repL_mul (repL_gP k) ih

@[expose] def Xs : Subgroup P45 := Subgroup.closure ({x45, y45} : Set P45)

theorem x45_mem : x45 ∈ Xs := Subgroup.subset_closure (by simp)

theorem y45_mem : y45 ∈ Xs := Subgroup.subset_closure (by simp)

theorem gP_mem (k : ℕ) : gP k ∈ Xs := by
  unfold gP
  split_ifs
  · exact x45_mem
  · exact y45_mem
  · exact Xs.inv_mem y45_mem

theorem wordP_mem (w : List ℕ) : wordP w ∈ Xs := by
  induction w with
  | nil => exact Xs.one_mem
  | cons k w ih => exact Xs.mul_mem (gP_mem k) ih

theorem gP_invLet (k : ℕ) : gP (invLet k) = (gP k)⁻¹ := by
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · simp only [invLet, gP, h]
    simpa using eq_inv_of_mul_eq_one_left x45_mul_self
  · simp [invLet, gP, h]
  · simp [invLet, gP, h]

theorem wordP_append (a b : List ℕ) : wordP (a ++ b) = wordP a * wordP b := by
  simp [wordP, List.map_append, List.prod_append]

theorem wordP_invW (w : List ℕ) : wordP (invW w) = (wordP w)⁻¹ := by
  induction w with
  | nil => simp [invW, wordP]
  | cons k w ih =>
    have : invW (k :: w) = invW w ++ [invLet k] := by simp [invW]
    rw [this, wordP_append, ih, show wordP [invLet k] = gP (invLet k) by simp [wordP],
      gP_invLet, show wordP (k :: w) = gP k * wordP w by simp [wordP], mul_inv_rev]

theorem applyW_eq (w : List ℕ) (p : Fin 45) : ((wordP w) p : ℕ) = applyW w p := by
  induction w with
  | nil => simp [wordP, applyW]
  | cons k w ih =>
    have h := (repL_gP k).2 ((wordP w) p)
    have e : wordP (k :: w) = gP k * wordP w := by simp [wordP]
    rw [e, Equiv.Perm.mul_apply, ← h, ih]
    simp [applyW]

end CFSG.Quasithin.H13.F431.U42
