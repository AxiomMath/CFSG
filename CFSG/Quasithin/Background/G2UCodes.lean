module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.QuadraticAlgebra.Defs
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.G2U

@[expose] def bz (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem bz_xor (a b : Bool) : bz (a ^^ b) = bz a + bz b := by
  cases a <;> cases b <;> decide

private theorem bz_injective : Function.Injective bz := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[expose] def dec2 (m : List ℕ) : Matrix (Fin 14) (Fin 14) (ZMod 2) :=
  Matrix.of fun i j => bz ((m.getD i 0).testBit j)

@[expose] def rowMul (r : ℕ) (n : List ℕ) : ℕ :=
  (List.range 14).foldr (fun k acc => if r.testBit k then n.getD k 0 ^^^ acc else acc) 0

@[expose] def mul2 (m n : List ℕ) : List ℕ :=
  m.map fun r => rowMul r n

private theorem bz_testBit_foldr (r j : ℕ) (n : List ℕ) (l : List ℕ) :
    bz ((l.foldr (fun k acc => if r.testBit k then n.getD k 0 ^^^ acc else acc) 0).testBit j) =
      (l.map fun k => bz (r.testBit k) * bz ((n.getD k 0).testBit j)).sum := by
  induction l with
  | nil => simp [bz]
  | cons k l ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    by_cases h : r.testBit k
    · rw [ite_eq_left h, Nat.testBit_xor, bz_xor, ih, h]
      simp [bz]
    · rw [ite_eq_right h, ih, Bool.eq_false_iff.mpr h]
      simp [bz]

private theorem rowMul_zero (n : List ℕ) : rowMul 0 n = 0 := by
  unfold rowMul
  induction (List.range 14) with
  | nil => rfl
  | cons k l ih => simp

private theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem dec2_mul2 (m n : List ℕ) : dec2 (mul2 m n) = dec2 m * dec2 n := by
  ext i j
  have hrow : (mul2 m n).getD i 0 = rowMul (m.getD i 0) n := by
    have h := List.getD_map m 0 (n := (i : ℕ)) (fun r => rowMul r n)
    rwa [rowMul_zero] at h
  rw [Matrix.mul_apply]
  change bz (((mul2 m n).getD i 0).testBit j) = _
  rw [hrow, rowMul, bz_testBit_foldr, list_sum_range,
    ← Fin.sum_univ_eq_sum_range (fun k => bz ((m.getD i 0).testBit k) *
      bz ((n.getD k 0).testBit j)) 14]
  rfl

@[expose] def id2 : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192]

theorem dec2_id2 : dec2 id2 = 1 := by
  decide

@[expose] def canon2 (m : List ℕ) : Bool :=
  m.length == 14 && m.all (· < 2 ^ 14)

theorem dec2_injective {m m' : List ℕ} (h : canon2 m = true) (h' : canon2 m' = true)
    (e : dec2 m = dec2 m') : m = m' := by
  simp only [canon2, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h h'
  refine List.ext_getElem (h.1.trans h'.1.symm) fun i hi hi' => Nat.eq_of_testBit_eq fun j => ?_
  have hi14 : i < 14 := h.1 ▸ hi
  by_cases hj : j < 14
  · have := congrFun (congrFun e ⟨i, hi14⟩) ⟨j, hj⟩
    simp only [dec2, Matrix.of_apply, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ hi'] at this
    exact bz_injective this
  · have h2 : 2 ^ 14 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj)
    rw [Nat.testBit_eq_false_of_lt ((h.2 _ (List.getElem_mem hi)).trans_le h2),
      Nat.testBit_eq_false_of_lt ((h'.2 _ (List.getElem_mem hi')).trans_le h2)]

instance : Fact (∀ r : ZMod 3, r ^ 2 ≠ -1 + 0 * r) :=
  ⟨by decide⟩

abbrev F9 : Type :=
  QuadraticAlgebra (ZMod 3) (-1) 0

theorem card_F9 : Nat.card F9 = 9 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0), Nat.card_prod,
    Nat.card_zmod]

@[expose] def dec9 (x : ℕ) : F9 :=
  ⟨((x % 3 : ℕ) : ZMod 3), ((x / 3 : ℕ) : ZMod 3)⟩

@[expose] def add9 (x y : ℕ) : ℕ :=
  (x % 3 + y % 3) % 3 + 3 * ((x / 3 + y / 3) % 3)

@[expose] def mul9 (x y : ℕ) : ℕ :=
  (x % 3 * (y % 3) + 2 * (x / 3 * (y / 3))) % 3 + 3 * ((x % 3 * (y / 3) + x / 3 * (y % 3)) % 3)

private theorem mod_div_aux (P Q : ℕ) :
    (P % 3 + 3 * (Q % 3)) % 3 = P % 3 ∧ (P % 3 + 3 * (Q % 3)) / 3 = Q % 3 := by
  omega

theorem dec9_add9 (x y : ℕ) : dec9 (add9 x y) = dec9 x + dec9 y := by
  obtain ⟨h1, h2⟩ := mod_div_aux (x % 3 + y % 3) (x / 3 + y / 3)
  ext
  · simp only [dec9, add9, h1, QuadraticAlgebra.re_add, ZMod.natCast_mod, Nat.cast_add]
  · simp only [dec9, add9, h2, QuadraticAlgebra.im_add, ZMod.natCast_mod, Nat.cast_add]

theorem dec9_mul9 (x y : ℕ) : dec9 (mul9 x y) = dec9 x * dec9 y := by
  obtain ⟨h1, h2⟩ := mod_div_aux (x % 3 * (y % 3) + 2 * (x / 3 * (y / 3)))
    (x % 3 * (y / 3) + x / 3 * (y % 3))
  have h3 : (2 : ZMod 3) = -1 := by decide
  ext
  · simp only [dec9, mul9, h1, QuadraticAlgebra.re_mul, ZMod.natCast_mod, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, h3]
    ring
  · simp only [dec9, mul9, h2, QuadraticAlgebra.im_mul, ZMod.natCast_mod, Nat.cast_add,
      Nat.cast_mul]
    ring

@[expose] def dec3 (m : List ℕ) : Matrix (Fin 3) (Fin 3) F9 :=
  Matrix.of fun i j => dec9 (m.getD (3 * i + j) 0)

@[expose] def ent3 (m n : List ℕ) (i j : ℕ) : ℕ :=
  add9 (add9 (mul9 (m.getD (3 * i) 0) (n.getD j 0))
      (mul9 (m.getD (3 * i + 1) 0) (n.getD (3 + j) 0)))
    (mul9 (m.getD (3 * i + 2) 0) (n.getD (6 + j) 0))

@[expose] def mul3 (m n : List ℕ) : List ℕ :=
  [ent3 m n 0 0, ent3 m n 0 1, ent3 m n 0 2, ent3 m n 1 0, ent3 m n 1 1, ent3 m n 1 2,
    ent3 m n 2 0, ent3 m n 2 1, ent3 m n 2 2]

theorem dec3_mul3 (m n : List ℕ) : dec3 (mul3 m n) = dec3 m * dec3 n := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [dec3, mul3, ent3, dec9_add9, dec9_mul9, add_assoc]

@[expose] def id3 : List ℕ :=
  [1, 0, 0, 0, 1, 0, 0, 0, 1]

theorem dec3_id3 : dec3 id3 = 1 := by
  decide

@[expose] def canon3 (m : List ℕ) : Bool :=
  m.length == 9 && m.all (· < 9)

private theorem dec9_injective : ∀ x < 9, ∀ y < 9, dec9 x = dec9 y → x = y := by
  decide

theorem dec3_injective {m m' : List ℕ} (h : canon3 m = true) (h' : canon3 m' = true)
    (e : dec3 m = dec3 m') : m = m' := by
  simp only [canon3, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h h'
  refine List.ext_getElem (h.1.trans h'.1.symm) fun t ht ht' => ?_
  have ht9 : t < 9 := h.1 ▸ ht
  have := congrFun (congrFun e ⟨t / 3, by omega⟩) ⟨t % 3, by omega⟩
  have hdm : 3 * (t / 3) + t % 3 = t := Nat.div_add_mod t 3
  simp only [dec3, Matrix.of_apply, hdm, List.getD_eq_getElem _ _ ht,
    List.getD_eq_getElem _ _ ht'] at this
  exact dec9_injective _ (h.2 _ (List.getElem_mem ht)) _ (h'.2 _ (List.getElem_mem ht')) this

end CFSG.Quasithin.G2U
