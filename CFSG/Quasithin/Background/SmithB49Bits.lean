module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
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
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.B5.B49

open Matrix

@[expose] def bitZ (x k : ℕ) : ZMod 2 := if x.testBit k then 1 else 0

theorem bitZ_xor (x y k : ℕ) : bitZ (x ^^^ y) k = bitZ x k + bitZ y k := by
  unfold bitZ
  rw [Nat.testBit_xor]
  cases x.testBit k <;> cases y.testBit k <;> decide

theorem bitZ_zero_left (k : ℕ) : bitZ 0 k = 0 := by
  simp [bitZ]

theorem bitZ_div_two (x k : ℕ) : bitZ (x / 2) k = bitZ x (k + 1) := by
  unfold bitZ
  rw [Nat.testBit_div_two]

theorem bitZ_two_pow (i k : ℕ) : bitZ (2 ^ i) k = if i = k then 1 else 0 := by
  unfold bitZ
  rw [Nat.testBit_two_pow]
  by_cases h : i = k <;> simp [h]

@[expose] def bxor : ℕ → List ℕ → ℕ
  | _, [] => 0
  | a, b :: bs => (if a % 2 = 1 then b else 0) ^^^ bxor (a / 2) bs

@[expose] def bmul (d : ℕ) (A B : List ℕ) : List ℕ :=
  A.map fun a => bxor a (B.take d)

@[expose] def badd : List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs => (a ^^^ b) :: badd as bs
  | as, [] => as
  | [], bs => bs

@[expose] def bone (d : ℕ) : List ℕ :=
  (List.range d).map (2 ^ ·)

theorem bxor_zero_left (B : List ℕ) : bxor 0 B = 0 := by
  induction B with
  | nil => rfl
  | cons b bs ih =>
    show (if 0 % 2 = 1 then b else 0) ^^^ bxor (0 / 2) bs = 0
    rw [Nat.zero_div, ih]
    simp

theorem bitZ_ite (a b j : ℕ) : bitZ (if a % 2 = 1 then b else 0) j = bitZ a 0 * bitZ b j := by
  by_cases h : a % 2 = 1
  · have : bitZ a 0 = 1 := by simp [bitZ, Nat.testBit_zero, h]
    rw [ite_eq_left h, this, one_mul]
  · have : bitZ a 0 = 0 := by simp [bitZ, Nat.testBit_zero, h]
    rw [ite_eq_right h, this, zero_mul, bitZ_zero_left]

theorem bitZ_bxor (a : ℕ) (B : List ℕ) (j : ℕ) :
    bitZ (bxor a B) j = ∑ k ∈ Finset.range B.length, bitZ a k * bitZ (B.getD k 0) j := by
  induction B generalizing a with
  | nil => simp [bxor, bitZ_zero_left]
  | cons b bs ih =>
    show bitZ ((if a % 2 = 1 then b else 0) ^^^ bxor (a / 2) bs) j = _
    rw [bitZ_xor, bitZ_ite, ih, List.length_cons, Finset.sum_range_succ']
    simp only [bitZ_div_two, List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

theorem getD_bmul (d : ℕ) (A B : List ℕ) (i : ℕ) :
    (bmul d A B).getD i 0 = bxor (A.getD i 0) (B.take d) := by
  have h := List.getD_map A 0 (n := i) (fun a => bxor a (B.take d))
  rw [bxor_zero_left] at h
  exact h

theorem getD_badd (A B : List ℕ) (i : ℕ) :
    (badd A B).getD i 0 = A.getD i 0 ^^^ B.getD i 0 := by
  induction A generalizing B i with
  | nil =>
    cases B with
    | nil => simp [badd]
    | cons b bs => simp [badd]
  | cons a as ih =>
    cases B with
    | nil => simp [badd]
    | cons b bs =>
      cases i with
      | zero => simp [badd]
      | succ i =>
        show ((a ^^^ b) :: badd as bs).getD (i + 1) 0 = _
        rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, ih]

theorem getD_take_of_lt (B : List ℕ) {d i : ℕ} (hi : i < d) :
    (B.take d).getD i 0 = B.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true]

theorem getD_bone (d i : ℕ) : (bone d).getD i 0 = if i < d then 2 ^ i else 0 := by
  unfold bone
  by_cases h : i < d
  · rw [ite_eq_left h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
    rfl
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_map]
    have : (List.range d)[i]? = none := by
      rw [List.getElem?_eq_none]
      simpa using h
    rw [this]
    rfl

variable {ι : Type*} {d : ℕ}

@[expose] def decM (e : ι ≃ Fin d) (A : List ℕ) : Matrix ι ι (ZMod 2) :=
  Matrix.of fun p q => bitZ (A.getD (e p) 0) (e q)

theorem decM_apply (e : ι ≃ Fin d) (A : List ℕ) (p q : ι) :
    decM e A p q = bitZ (A.getD (e p) 0) (e q) := rfl

theorem sum_range_eq [Fintype ι] (e : ι ≃ Fin d) (f : ℕ → ZMod 2) :
    ∑ k ∈ Finset.range d, f k = ∑ r : ι, f (e r) := by
  rw [Finset.sum_range]
  exact (Equiv.sum_comp e (fun k : Fin d => f k)).symm

theorem decM_bmul [Fintype ι] (e : ι ≃ Fin d) (A B : List ℕ) :
    decM e (bmul d A B) = decM e A * decM e B := by
  ext p q
  rw [decM_apply, getD_bmul, bitZ_bxor, Matrix.mul_apply]
  set f : ℕ → ZMod 2 := fun k => bitZ (A.getD (e p) 0) k * bitZ ((B.take d).getD k 0) (e q)
    with hf
  have hlen : (B.take d).length ≤ d := List.length_take_le d B
  have h0 : ∑ k ∈ Finset.Ico (B.take d).length d, f k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [hf]
    simp only
    rw [List.getD_eq_default _ _ hk.1, bitZ_zero_left, mul_zero]
  have key : ∑ k ∈ Finset.range (B.take d).length, f k = ∑ k ∈ Finset.range d, f k := by
    rw [← Finset.sum_range_add_sum_Ico f hlen, h0, add_zero]
  rw [key, sum_range_eq e]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hf]
  simp only
  rw [decM_apply, decM_apply, getD_take_of_lt B (e r).2]

theorem decM_badd (e : ι ≃ Fin d) (A B : List ℕ) :
    decM e (badd A B) = decM e A + decM e B := by
  ext p q
  rw [Matrix.add_apply, decM_apply, decM_apply, decM_apply, getD_badd, bitZ_xor]

theorem decM_nil (e : ι ≃ Fin d) : decM e [] = 0 := by
  ext p q
  rw [decM_apply, List.getD_nil, bitZ_zero_left]
  rfl

theorem decM_bone [DecidableEq ι] (e : ι ≃ Fin d) : decM e (bone d) = 1 := by
  ext p q
  rw [decM_apply, getD_bone, ite_eq_left (e p).2, bitZ_two_pow, one_apply]
  by_cases h : p = q
  · subst h
    simp
  · have : (e p : ℕ) ≠ e q := fun h' => h (e.injective (Fin.ext h'))
    simp [h, this]

@[expose] def foxD [Fintype ι] [DecidableEq ι] {k : ℕ} (A : Fin k → Matrix ι ι (ZMod 2)) :
    List (Fin k) → Fin k → Matrix ι ι (ZMod 2)
  | [], _ => 0
  | i :: w, l => (if i = l then 1 else 0) + A i * foxD A w l

@[expose] def foxDB {k : ℕ} (d : ℕ) (A : Fin k → List ℕ) : List (Fin k) → Fin k → List ℕ
  | [], _ => []
  | i :: w, l => badd (if i = l then bone d else []) (bmul d (A i) (foxDB d A w l))

theorem decM_foxDB [Fintype ι] [DecidableEq ι] {k : ℕ} (e : ι ≃ Fin d) (A : Fin k → List ℕ)
    (w : List (Fin k)) (l : Fin k) :
    decM e (foxDB d A w l) = foxD (fun i => decM e (A i)) w l := by
  induction w with
  | nil => exact decM_nil e
  | cons i w ih =>
    show decM e (badd (if i = l then bone d else []) (bmul d (A i) (foxDB d A w l))) =
      (if i = l then 1 else 0) + decM e (A i) * foxD (fun i => decM e (A i)) w l
    rw [decM_badd, decM_bmul, ih]
    by_cases h : i = l
    · rw [ite_eq_left h, ite_eq_left h, decM_bone]
    · rw [ite_eq_right h, ite_eq_right h, decM_nil]

@[expose] def bsum {α : Type*} (f : α → List ℕ) : List α → List ℕ
  | [] => []
  | a :: as => badd (f a) (bsum f as)

theorem decM_bsum {α : Type*} (e : ι ≃ Fin d) (f : α → List ℕ) (L : List α) :
    decM e (bsum f L) = (L.map fun a => decM e (f a)).sum := by
  induction L with
  | nil => exact decM_nil e
  | cons a as ih =>
    show decM e (badd (f a) (bsum f as)) = _
    rw [decM_badd, ih, List.map_cons, List.sum_cons]

theorem decM_bsum_finRange {m : ℕ} (e : ι ≃ Fin d) (f : Fin m → List ℕ) :
    decM e (bsum f (List.finRange m)) = ∑ r, decM e (f r) := by
  rw [decM_bsum, Fin.sum_univ_def]

end CFSG.Quasithin.B5.B49
