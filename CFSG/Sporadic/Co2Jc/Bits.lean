module

public import CFSG.Sporadic.Co2Smith.GlNJInputs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Co2Jc

@[expose] def colAct (c : ℕ → ℕ) (x : ℕ) : ℕ :=
  (List.range 10).foldr (fun i acc => if x.testBit i then c i ^^^ acc else acc) 0

theorem glNJT_eq_colAct (k x : ℕ) :
    Co2Smith.Native.glNJT k x = colAct (fun i => (Co2Smith.Native.glNJTab[k]!)[i]!) x := rfl

private theorem colAct_foldr_zero (c : ℕ → ℕ) (l : List ℕ) (x : ℕ)
    (h : ∀ i ∈ l, x.testBit i = false) :
    l.foldr (fun i acc => if x.testBit i then c i ^^^ acc else acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hi : x.testBit i = false := h i (by simp)
    have hl : ∀ j ∈ l, x.testBit j = false := fun j hj => h j (by simp [hj])
    rw [List.foldr_cons, hi, ih hl]
    simp

private theorem xor_common (a b c : ℕ) : (a ^^^ b) ^^^ (a ^^^ c) = b ^^^ c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

private theorem xor_assoc_comm (a b c : ℕ) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

private theorem colAct_foldr_xor (c : ℕ → ℕ) (l : List ℕ) (x y : ℕ) :
    l.foldr (fun i acc => if (x ^^^ y).testBit i then c i ^^^ acc else acc) 0 =
      l.foldr (fun i acc => if x.testBit i then c i ^^^ acc else acc) 0 ^^^
        l.foldr (fun i acc => if y.testBit i then c i ^^^ acc else acc) 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.foldr_cons, ih, Nat.testBit_xor]
    cases hx : x.testBit i <;> cases hy : y.testBit i <;>
      simp [hx, hy, xor_common, xor_assoc_comm, Nat.xor_assoc]

theorem colAct_zero (c : ℕ → ℕ) : colAct c 0 = 0 :=
  colAct_foldr_zero c (List.range 10) 0 (by simp)

theorem colAct_xor (c : ℕ → ℕ) (x y : ℕ) : colAct c (x ^^^ y) = colAct c x ^^^ colAct c y :=
  colAct_foldr_xor c (List.range 10) x y

private theorem colAct_foldr_pow (c : ℕ → ℕ) (i n : ℕ) (a : ℕ) :
    (List.range n).foldr (fun j acc => if (2 ^ i).testBit j then c j ^^^ acc else acc) a =
      if i < n then c i ^^^ a else a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [ih]
    by_cases hi : i < n
    · have hne : i ≠ n := by omega
      have hlt : i < n + 1 := by omega
      rw [if_pos hi, if_pos hlt]
      simp [Nat.testBit_two_pow, hne]
    · by_cases heq : i = n
      · simp [heq, hi, Nat.testBit_two_pow]
      · have hlt : ¬ i < n + 1 := by omega
        rw [if_neg hi, if_neg hlt]
        simp [Nat.testBit_two_pow, heq]

theorem colAct_two_pow (c : ℕ → ℕ) {i : ℕ} (hi : i < 10) : colAct c (2 ^ i) = c i := by
  unfold colAct
  rw [colAct_foldr_pow c i 10 0, if_pos hi, Nat.xor_zero]

private theorem colAct_foldr_lt (c : ℕ → ℕ) (l : List ℕ) (x : ℕ)
    (hc : ∀ i ∈ l, c i < 1024) :
    l.foldr (fun i acc => if x.testBit i then c i ^^^ acc else acc) 0 < 1024 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.foldr_cons]
    have hi : c i < 1024 := hc i (by simp)
    have hl : ∀ j ∈ l, c j < 1024 := fun j hj => hc j (by simp [hj])
    have ih' := ih hl
    split_ifs
    · have h1024 : (1024 : ℕ) = 2 ^ 10 := by norm_num
      rw [h1024] at hi ih' ⊢
      exact Nat.xor_lt_two_pow hi ih'
    · exact ih'

theorem colAct_lt {c : ℕ → ℕ} (hc : ∀ i < 10, c i < 1024) (x : ℕ) : colAct c x < 1024 :=
  colAct_foldr_lt c (List.range 10) x (fun i hi => hc i (List.mem_range.1 hi))

@[expose] def xorList (l : List ℕ) : ℕ := l.foldr (· ^^^ ·) 0

@[expose] def bsum (n m : ℕ) (v : ℕ → ZMod 2) : ZMod 2 :=
  ∑ i ∈ Finset.range n, if m.testBit i then v i else 0

theorem bsum_zero (n : ℕ) (v : ℕ → ZMod 2) : bsum n 0 v = 0 := by
  simp [bsum]

theorem bsum_xor (n m m' : ℕ) (v : ℕ → ZMod 2) :
    bsum n (m ^^^ m') v = bsum n m v + bsum n m' v := by
  have hxx : ∀ a : ZMod 2, a + a = 0 := by decide
  simp only [bsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_xor]
  cases hm : m.testBit i <;> cases hm' : m'.testBit i <;> simp [hm, hm', hxx]

theorem bsum_two_pow {n i : ℕ} (hi : i < n) (v : ℕ → ZMod 2) : bsum n (2 ^ i) v = v i := by
  rw [bsum, Finset.sum_eq_single i]
  · simp [Nat.testBit_two_pow]
  · intro j _ hj
    rw [Nat.testBit_two_pow]
    have : i ≠ j := fun h => hj h.symm
    simp [this]
  · intro h
    exact absurd (Finset.mem_range.2 hi) h

theorem bsum_xorList (n : ℕ) (l : List ℕ) (v : ℕ → ZMod 2) :
    bsum n (xorList l) v = (l.map fun m => bsum n m v).sum := by
  induction l with
  | nil => simp [xorList, bsum_zero]
  | cons a l ih =>
    rw [xorList, List.foldr_cons, bsum_xor]
    change bsum n a v + bsum n (xorList l) v = (bsum n a v) +
      (List.map (fun m => bsum n m v) l).sum
    rw [ih]

theorem bsum_xorList_eq_zero {n : ℕ} {l : List ℕ} {v : ℕ → ZMod 2}
    (h : ∀ m ∈ l, bsum n m v = 0) : bsum n (xorList l) v = 0 := by
  induction l with
  | nil => simp [xorList, bsum_zero]
  | cons a l ih =>
    rw [xorList, List.foldr_cons, bsum_xor]
    change bsum n a v + bsum n (xorList l) v = 0
    rw [h a (by simp), ih (fun m hm => h m (by simp [hm])), zero_add]

end CFSG.Sporadic.Co2Jc
