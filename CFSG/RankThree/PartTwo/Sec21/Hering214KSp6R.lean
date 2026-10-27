module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214.Sp6R

open Finset

@[expose] def bit (n j : ℕ) : ZMod 2 := if n.testBit j then 1 else 0

theorem bit_xor (a b j : ℕ) : bit (a ^^^ b) j = bit a j + bit b j := by
  unfold bit
  rw [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

theorem bit_zero (j : ℕ) : bit 0 j = 0 := by simp [bit]

@[expose] def dr (A : List ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => bit (A.getD i 0) j

@[expose] def xorFold (r : ℕ) (B : List ℕ) : ℕ :=
  (List.range 6).foldl (fun acc j => if r.testBit j then acc ^^^ B.getD j 0 else acc) 0

@[expose] def mulR (A B : List ℕ) : List ℕ := A.map fun r => xorFold r B

@[expose] def oneR : List ℕ := [1, 2, 4, 8, 16, 32]

@[expose] def zeroR : List ℕ := [0, 0, 0, 0, 0, 0]

@[expose] def addR (A B : List ℕ) : List ℕ := List.zipWith (· ^^^ ·) A B

@[expose] def powR (A : List ℕ) (n : ℕ) : List ℕ :=
  (List.range n).foldl (fun acc _ => mulR acc A) oneR

theorem sum_range_list {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Fin.sum_univ_castSucc]
    simp

theorem bit_foldl (r : ℕ) (B : List ℕ) (l : List ℕ) (acc j : ℕ) :
    bit (l.foldl (fun a k => if r.testBit k then a ^^^ B.getD k 0 else a) acc) j =
      bit acc j + (l.map fun k => bit r k * bit (B.getD k 0) j).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons k l ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    by_cases h : r.testBit k
    · rw [if_pos h, ih, bit_xor]
      have hb : bit r k = 1 := by simp [bit, h]
      rw [hb, one_mul]
      ring
    · rw [if_neg h, ih]
      have hb : bit r k = 0 := by simp [bit, h]
      rw [hb, zero_mul]
      ring

theorem bit_xorFold (r : ℕ) (B : List ℕ) (j : ℕ) :
    bit (xorFold r B) j = ∑ k : Fin 6, bit r k * bit (B.getD k 0) j := by
  unfold xorFold
  rw [bit_foldl, bit_zero, zero_add,
    sum_range_list (fun k => bit r k * bit (B.getD k 0) j) 6]

theorem getD_mulR (A B : List ℕ) (i : ℕ) : (mulR A B).getD i 0 = xorFold (A.getD i 0) B := by
  have h0 : xorFold 0 B = 0 := by simp [xorFold, Nat.zero_testBit]
  have := List.getD_map (f := fun r => xorFold r B) (l := A) (n := i) (d := 0)
  rw [h0] at this
  exact this

theorem dr_mulR (A B : List ℕ) : dr (mulR A B) = dr A * dr B := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [dr, Matrix.of_apply]
  rw [getD_mulR, bit_xorFold]

theorem dr_oneR : dr oneR = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dr, oneR, bit, Nat.testBit]

theorem dr_zeroR : dr zeroR = 0 := by
  ext i j
  fin_cases i <;> simp [dr, zeroR, bit_zero]

theorem dr_powR (A : List ℕ) (n : ℕ) : dr (powR A n) = dr A ^ n := by
  induction n with
  | zero => simp [powR, dr_oneR]
  | succ n ih =>
    rw [powR, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← powR,
      dr_mulR, ih, pow_succ]

@[expose] def Canon (A : List ℕ) : Prop := A.length = 6 ∧ ∀ r ∈ A, r < 64

theorem canon_oneR : Canon oneR := by
  refine ⟨rfl, ?_⟩
  decide

theorem getD_lt {B : List ℕ} (hB : ∀ r ∈ B, r < 64) (k : ℕ) : B.getD k 0 < 64 := by
  by_cases hk : k < B.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hB _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem xorFold_lt {B : List ℕ} (hB : ∀ r ∈ B, r < 64) (r : ℕ) : xorFold r B < 64 := by
  have key : ∀ (l : List ℕ) (acc : ℕ), acc < 64 →
      l.foldl (fun a k => if r.testBit k then a ^^^ B.getD k 0 else a) acc < 64 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons k l ih =>
      intro acc h
      rw [List.foldl_cons]
      apply ih
      split_ifs
      · exact Nat.xor_lt_two_pow (n := 6) h (getD_lt hB k)
      · exact h
  exact key _ 0 (by norm_num)

theorem canon_mulR {A B : List ℕ} (hA : A.length = 6) (hB : ∀ r ∈ B, r < 64) :
    Canon (mulR A B) := by
  refine ⟨by simp [mulR, hA], ?_⟩
  intro r hr
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hr
  exact xorFold_lt hB x

theorem canon_powR {A : List ℕ} (hA : Canon A) (n : ℕ) : Canon (powR A n) := by
  induction n with
  | zero => exact canon_oneR
  | succ n ih =>
    rw [powR, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← powR]
    exact canon_mulR ih.1 hA.2

theorem dr_addR {A B : List ℕ} (hA : A.length = 6) (hB : B.length = 6) :
    dr (addR A B) = dr A + dr B := by
  ext i j
  simp only [dr, Matrix.of_apply, Matrix.add_apply]
  have hi : (i : ℕ) < (addR A B).length := by simp [addR, hA, hB]
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega : (i : ℕ) < A.length),
    List.getD_eq_getElem _ _ (by omega : (i : ℕ) < B.length)]
  simp only [addR, List.getElem_zipWith]
  exact bit_xor _ _ _

theorem dr_inj {A B : List ℕ} (hA : Canon A) (hB : Canon B) (h : dr A = dr B) : A = B := by
  apply List.ext_getElem (hA.1.trans hB.1.symm)
  intro i hi hi'
  have hi6 : i < 6 := hA.1 ▸ hi
  have hrow : A.getD i 0 = B.getD i 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 6
    · have := congrFun (congrFun h ⟨i, hi6⟩) ⟨j, hj⟩
      simp only [dr, Matrix.of_apply, bit] at this
      cases ha : (A.getD i 0).testBit j <;> cases hb : (B.getD i 0).testBit j <;>
        simp_all
    · have hla := getD_lt hA.2 i
      have hlb := getD_lt hB.2 i
      have h64 : (64 : ℕ) ≤ 2 ^ j := by
        calc (64 : ℕ) = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hla h64),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlb h64)]
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at hrow
  exact hrow

theorem length_mulR (A B : List ℕ) : (mulR A B).length = A.length := by simp [mulR]

theorem length_powR {A : List ℕ} (hA : A.length = 6) (n : ℕ) : (powR A n).length = 6 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [powR, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← powR,
      length_mulR, ih]

theorem length_addR {A B : List ℕ} (hA : A.length = 6) (hB : B.length = 6) :
    (addR A B).length = 6 := by simp [addR, hA, hB]

@[expose] def Vr (v : ℕ) : List ℕ := (List.range 6).map fun r => (v >>> r) &&& 1

@[expose] def Er (m : ℕ) : List ℕ := [1 <<< m, 0, 0, 0, 0, 0]

@[expose] def gOf (A B : List ℕ) (w : ℕ) : List ℕ := mulR (powR A (w / 3)) (powR B (w % 3))

@[expose] def Kr (A B ws : List ℕ) (v : ℕ) : List ℕ :=
  (List.range 6).foldl
    (fun acc m => addR acc (mulR (mulR (gOf A B (ws.getD m 0)) (Vr v)) (Er m))) zeroR

@[expose] def cycChk (A B ws : List ℕ) (v : ℕ) (Kinv : List ℕ) : Bool :=
  mulR (Kr A B ws v) Kinv == oneR &&
    (List.range 64).all fun w =>
      !(mulR (mulR (Kr A B ws w) Kinv) (mulR (Kr A B ws w) Kinv) == oneR) ||
        mulR (Kr A B ws w) Kinv == oneR

theorem length_gOf {A B : List ℕ} (hA : A.length = 6) (hB : B.length = 6) (w : ℕ) :
    (gOf A B w).length = 6 := by
  rw [gOf, length_mulR, length_powR hA]

theorem length_Vr (v : ℕ) : (Vr v).length = 6 := by simp [Vr]

theorem dr_foldl_addR (T : ℕ → List ℕ) (hT : ∀ m, (T m).length = 6) (l : List ℕ)
    (acc : List ℕ) (hacc : acc.length = 6) :
    dr (l.foldl (fun a m => addR a (T m)) acc) = dr acc + (l.map fun m => dr (T m)).sum ∧
      (l.foldl (fun a m => addR a (T m)) acc).length = 6 := by
  induction l generalizing acc with
  | nil => simp [hacc]
  | cons m l ih =>
    have hlen : (addR acc (T m)).length = 6 := length_addR hacc (hT m)
    obtain ⟨h1, h2⟩ := ih (addR acc (T m)) hlen
    refine ⟨?_, ?_⟩
    · rw [List.foldl_cons, h1, dr_addR hacc (hT m), List.map_cons, List.sum_cons]
      abel
    · rw [List.foldl_cons]
      exact h2

theorem length_Kr {A B : List ℕ} (hA : A.length = 6) (hB : B.length = 6) (ws : List ℕ) (v : ℕ) :
    (Kr A B ws v).length = 6 := by
  refine (dr_foldl_addR (fun m => mulR (mulR (gOf A B (ws.getD m 0)) (Vr v)) (Er m)) ?_
    (List.range 6) zeroR rfl).2
  intro m
  rw [length_mulR, length_mulR, length_gOf hA hB]

theorem dr_Kr {A B : List ℕ} (hA : A.length = 6) (hB : B.length = 6) (ws : List ℕ) (v : ℕ) :
    dr (Kr A B ws v) =
      ∑ m : Fin 6, dr (gOf A B (ws.getD m 0)) * dr (Vr v) * dr (Er m) := by
  have hT : ∀ m : ℕ, (mulR (mulR (gOf A B (ws.getD m 0)) (Vr v)) (Er m)).length = 6 := by
    intro m
    rw [length_mulR, length_mulR, length_gOf hA hB]
  obtain ⟨h1, -⟩ := dr_foldl_addR (fun m => mulR (mulR (gOf A B (ws.getD m 0)) (Vr v)) (Er m))
    hT (List.range 6) zeroR rfl
  unfold Kr
  rw [h1, dr_zeroR, zero_add, sum_range_list
    (fun m => dr (mulR (mulR (gOf A B (ws.getD m 0)) (Vr v)) (Er m))) 6]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dr_mulR, dr_mulR]

theorem cyc_eq {M V Kinv : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    {g E : Fin 6 → Matrix (Fin 6) (Fin 6) (ZMod 2)} (hg : ∀ m, M * g m = g m * M)
    (hK : (∑ m, g m * V * E m) * Kinv = 1) :
    M = (∑ m, g m * (M * V) * E m) * Kinv := by
  have h : ∀ m, M * (g m * V * E m) = g m * (M * V) * E m := fun m => by
    calc M * (g m * V * E m) = (M * g m) * V * E m := by simp only [mul_assoc]
      _ = (g m * M) * V * E m := by rw [hg m]
      _ = g m * (M * V) * E m := by simp only [mul_assoc]
  calc M = M * ((∑ m, g m * V * E m) * Kinv) := by rw [hK, mul_one]
    _ = (∑ m, M * (g m * V * E m)) * Kinv := by rw [← mul_assoc, Finset.mul_sum]
    _ = (∑ m, g m * (M * V) * E m) * Kinv := by simp only [h]

theorem bit_val_zero (t : ZMod 2) : bit t.val 0 = t := by revert t; decide

theorem bit_val_succ (t : ZMod 2) (c : ℕ) (hc : c ≠ 0) : bit t.val c = 0 := by
  have hlt : t.val < 2 := ZMod.val_lt t
  have : t.val < 2 ^ c := lt_of_lt_of_le hlt (by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega))
  simp [bit, Nat.testBit_eq_false_of_lt this]

theorem sum_val_lt : ∀ d : Fin 6 → ZMod 2, (∑ r : Fin 6, (d r).val * 2 ^ (r : ℕ)) < 64 := by
  decide +kernel

theorem sum_val_bit : ∀ d : Fin 6 → ZMod 2, ∀ r : Fin 6,
    ((∑ r' : Fin 6, (d r').val * 2 ^ (r' : ℕ)) >>> (r : ℕ)) &&& 1 = (d r).val := by
  decide +kernel

theorem exists_Vr {N : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hN : ∀ r c, c ≠ 0 → N r c = 0) :
    ∃ w < 64, N = dr (Vr w) := by
  refine ⟨∑ r : Fin 6, (N r 0).val * 2 ^ (r : ℕ), sum_val_lt _, ?_⟩
  ext r c
  have hrow : (Vr (∑ r' : Fin 6, (N r' 0).val * 2 ^ (r' : ℕ))).getD r 0 = (N r 0).val := by
    have hr : (r : ℕ) < (Vr (∑ r' : Fin 6, (N r' 0).val * 2 ^ (r' : ℕ))).length := by
      rw [length_Vr]; exact r.2
    rw [List.getD_eq_getElem _ _ hr]
    simp only [Vr, List.getElem_map, List.getElem_range]
    exact sum_val_bit (fun r' => N r' 0) r
  simp only [dr, Matrix.of_apply]
  rw [hrow]
  by_cases hc : c = 0
  · subst hc
    have h0 : ((0 : Fin 6) : ℕ) = 0 := rfl
    rw [h0, bit_val_zero]
  · rw [bit_val_succ _ _ (fun h => hc (Fin.ext h)), hN r c hc]

theorem dr_Vr_apply_ne {v : ℕ} {r c : Fin 6} (hc : c ≠ 0) : dr (Vr v) r c = 0 := by
  simp only [dr, Matrix.of_apply]
  have hr : (r : ℕ) < (Vr v).length := by rw [length_Vr]; exact r.2
  rw [List.getD_eq_getElem _ _ hr]
  simp only [Vr, List.getElem_map, List.getElem_range]
  have hlt : (v >>> (r : ℕ)) &&& 1 < 2 ^ (c : ℕ) := by
    have h1 : (v >>> (r : ℕ)) &&& 1 ≤ 1 := Nat.and_le_right
    have h2 : 1 < 2 ^ (c : ℕ) := Nat.one_lt_two_pow (fun h => hc (Fin.ext h))
    omega
  unfold bit
  rw [Nat.testBit_eq_false_of_lt hlt]
  simp

theorem eq_one_of_cycChk {A B ws Kinv : List ℕ} {v : ℕ} (hA : Canon A) (hB : Canon B)
    (hKinv : Canon Kinv) (h : cycChk A B ws v Kinv = true)
    {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hMA : M * dr A = dr A * M)
    (hMB : M * dr B = dr B * M) (hM : M * M = 1) : M = 1 := by
  simp only [cycChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq] at h
  obtain ⟨hKlist, hdec⟩ := h
  have hg : ∀ m : Fin 6, M * dr (gOf A B (ws.getD m 0)) = dr (gOf A B (ws.getD m 0)) * M := by
    intro m
    rw [gOf, dr_mulR, dr_powR, dr_powR]
    exact ((Commute.pow_right (show Commute M (dr A) from hMA) _).mul_right
      (Commute.pow_right (show Commute M (dr B) from hMB) _)).eq
  have hK : (∑ m : Fin 6, dr (gOf A B (ws.getD m 0)) * dr (Vr v) * dr (Er m)) * dr Kinv = 1 := by
    rw [← dr_Kr hA.1 hB.1, ← dr_mulR, hKlist, dr_oneR]
  have hMeq := cyc_eq hg hK
  have hN : ∀ r c, c ≠ 0 → (M * dr (Vr v)) r c = 0 := by
    intro r c hc
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun s _ => by rw [dr_Vr_apply_ne hc, mul_zero]
  obtain ⟨w, hw, hNw⟩ := exists_Vr hN
  rw [hNw, ← dr_Kr hA.1 hB.1, ← dr_mulR] at hMeq
  set Ph : List ℕ := mulR (Kr A B ws w) Kinv with hPh
  have hPhc : Canon Ph := canon_mulR (length_Kr hA.1 hB.1 ws w) hKinv.2
  have hsq : mulR Ph Ph = oneR := by
    apply dr_inj (canon_mulR hPhc.1 hPhc.2) canon_oneR
    rw [dr_mulR, dr_oneR, ← hMeq]
    exact hM
  have hPh1 : Ph = oneR := by
    have := hdec w hw
    rcases this with h1 | h1
    · exact absurd hsq h1
    · exact h1
  rw [hMeq, hPh1, dr_oneR]

end CFSG.RankThree.PartTwo.Sec21.Hering214.Sp6R
