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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.Sporadic.ThSchreier

@[expose] def bitZ (n i : ℕ) : ZMod 2 := if n.testBit i then 1 else 0

theorem bitZ_xor (m n i : ℕ) : bitZ (m ^^^ n) i = bitZ m i + bitZ n i := by
  simp only [bitZ, Nat.testBit_xor]
  cases m.testBit i <;> cases n.testBit i <;> decide

theorem bitZ_zero (i : ℕ) : bitZ 0 i = 0 := by simp [bitZ]

@[expose] def vec8 (v : ℕ) : Fin 8 → ZMod 2 := fun i => bitZ v i

@[expose] def mat8 (c : List ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => bitZ (c.getD j 0) i

@[expose] def app8 (c : List ℕ) (v : ℕ) : ℕ :=
  (List.range 8).foldl (fun acc j => if v.testBit j then acc ^^^ c.getD j 0 else acc) 0

@[expose] def mul8 (A B : List ℕ) : List ℕ := (List.range 8).map fun j => app8 A (B.getD j 0)

@[expose] def id8 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128]

@[expose] def zero8 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0]

theorem foldl_app_bitZ (c : List ℕ) (v i m : ℕ) :
    bitZ ((List.range m).foldl (fun acc j => if v.testBit j then acc ^^^ c.getD j 0 else acc) 0)
      i = ∑ j ∈ Finset.range m, bitZ v j * bitZ (c.getD j 0) i := by
  induction m with
  | zero => simp [bitZ_zero]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases h : v.testBit m
    · rw [ite_eq_left h, bitZ_xor]
      simp only [bitZ, h, ite_true, one_mul]
    · rw [ite_eq_right h]
      simp only [bitZ, h, Bool.false_eq_true, ite_false, zero_mul, add_zero]

theorem bitZ_app8 (c : List ℕ) (v i : ℕ) :
    bitZ (app8 c v) i = ∑ j : Fin 8, bitZ v j * bitZ (c.getD j 0) i := by
  rw [app8, foldl_app_bitZ, ← Fin.sum_univ_eq_sum_range (fun j => bitZ v j * bitZ (c.getD j 0) i)]

theorem mat8_mulVec (c : List ℕ) (v : ℕ) : (mat8 c).mulVec (vec8 v) = vec8 (app8 c v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, mat8, Matrix.of_apply, vec8]
  rw [bitZ_app8]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem mul8_getD (A B : List ℕ) {j : ℕ} (hj : j < 8) :
    (mul8 A B).getD j 0 = app8 A (B.getD j 0) := by
  rw [mul8, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem mat8_mul (A B : List ℕ) : mat8 (mul8 A B) = mat8 A * mat8 B := by
  ext i j
  simp only [mat8, Matrix.of_apply, Matrix.mul_apply]
  rw [mul8_getD A B j.isLt, bitZ_app8]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem mat8_id8 : mat8 id8 = 1 := by
  ext i j
  simp only [mat8, Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> decide

theorem mat8_zero8 : mat8 zero8 = 0 := by
  ext i j
  simp only [mat8, Matrix.of_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> decide

@[expose] def Norm8 (c : List ℕ) : Prop := c.length = 8 ∧ ∀ x ∈ c, x < 256

theorem getD_lt_256 {c : List ℕ} (hc : ∀ x ∈ c, x < 256) (j : ℕ) : c.getD j 0 < 256 := by
  by_cases hm : j < c.length
  · rw [List.getD_eq_getElem _ _ hm]
    exact hc _ (List.getElem_mem hm)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem mat8_injective {c d : List ℕ} (hc : Norm8 c) (hd : Norm8 d) (h : mat8 c = mat8 d) :
    c = d := by
  have key : ∀ j < 8, c.getD j 0 = d.getD j 0 := by
    intro j hj8
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · have := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj8⟩
      simp only [mat8, Matrix.of_apply, bitZ] at this
      revert this
      cases (c.getD j 0).testBit i <;> cases (d.getD j 0).testBit i <;> decide
    · have h256 : (256 : ℕ) ≤ 2 ^ i := by
        calc (256 : ℕ) = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (getD_lt_256 hc.2 j) h256),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (getD_lt_256 hd.2 j) h256)]
  refine List.ext_getElem (hc.1.trans hd.1.symm) fun j hj hj' => ?_
  have := key j (hc.1 ▸ hj)
  rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at this

theorem app8_lt (c : List ℕ) (hc : ∀ x ∈ c, x < 256) (v : ℕ) : app8 c v < 256 := by
  have key : ∀ (m acc : ℕ), acc < 256 →
      (List.range m).foldl (fun acc j => if v.testBit j then acc ^^^ c.getD j 0 else acc) acc
        < 256 := by
    intro m
    induction m with
    | zero => intro acc h; simpa using h
    | succ m ih =>
      intro acc h
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have h1 := ih acc h
      split_ifs
      · have h2 : c.getD m 0 < 256 := getD_lt_256 hc m
        have := Nat.xor_lt_two_pow (n := 8) (by simpa using h1) (by simpa using h2)
        simpa using this
      · exact h1
  exact key 8 0 (by norm_num)

theorem norm8_mul8 (A B : List ℕ) (hA : ∀ x ∈ A, x < 256) : Norm8 (mul8 A B) := by
  refine ⟨by simp [mul8], fun x hx => ?_⟩
  simp only [mul8, List.mem_map, List.mem_range] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact app8_lt A hA _

@[expose] def enc8 (v : Fin 8 → ZMod 2) : ℕ := ∑ i : Fin 8, (v i).val * 2 ^ i.val

end CFSG.Sporadic.ThSchreier
