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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.U3

open Matrix

@[expose] def bit2 (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bit2_xor (a b : Bool) : bit2 (a ^^ b) = bit2 a + bit2 b := by
  cases a <;> cases b <;> decide

theorem bit2_injective : Function.Injective bit2 := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[expose] def vecOf (v : ℕ) : Fin 6 → ZMod 2 := fun i => bit2 (v.testBit i)

@[expose] def colMat (m : List ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => bit2 ((m.getD j 0).testBit i)

@[expose] def vapp (m : List ℕ) (v : ℕ) : ℕ :=
  (List.range 6).foldr (fun j acc => if v.testBit j then m.getD j 0 ^^^ acc else acc) 0

@[expose] def mul6 (m n : List ℕ) : List ℕ :=
  n.map (vapp m)

@[expose] def id6 : List ℕ :=
  [1, 2, 4, 8, 16, 32]

theorem bit2_testBit_foldr (v i : ℕ) (m : List ℕ) (l : List ℕ) :
    bit2 ((l.foldr (fun j acc => if v.testBit j then m.getD j 0 ^^^ acc else acc) 0).testBit i) =
      (l.map fun j => bit2 ((m.getD j 0).testBit i) * bit2 (v.testBit j)).sum := by
  induction l with
  | nil => simp [bit2]
  | cons j l ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    by_cases h : v.testBit j
    · rw [ite_eq_left h, Nat.testBit_xor, bit2_xor, ih, h]
      simp [bit2]
    · rw [ite_eq_right h, ih, Bool.eq_false_iff.mpr h]
      simp [bit2]

theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem vapp_zero (m : List ℕ) : vapp m 0 = 0 := by
  unfold vapp
  induction (List.range 6) with
  | nil => rfl
  | cons k l ih => simp

theorem colMat_mulVec_vecOf (m : List ℕ) (v : ℕ) : colMat m *ᵥ vecOf v = vecOf (vapp m v) := by
  ext i
  change ∑ j, colMat m i j * vecOf v j = bit2 ((vapp m v).testBit i)
  rw [vapp, bit2_testBit_foldr, list_sum_map_range,
    ← Fin.sum_univ_eq_sum_range (fun j => bit2 ((m.getD j 0).testBit i) * bit2 (v.testBit j)) 6]
  rfl

theorem colMat_mul6 (m n : List ℕ) : colMat (mul6 m n) = colMat m * colMat n := by
  ext i j
  have hcol : (mul6 m n).getD j 0 = vapp m (n.getD j 0) := by
    have h := List.getD_map n 0 (n := (j : ℕ)) (vapp m)
    rwa [vapp_zero] at h
  rw [Matrix.mul_apply]
  change bit2 (((mul6 m n).getD j 0).testBit i) = _
  rw [hcol, vapp, bit2_testBit_foldr, list_sum_map_range,
    ← Fin.sum_univ_eq_sum_range
      (fun k => bit2 ((m.getD k 0).testBit i) * bit2 ((n.getD j 0).testBit k)) 6]
  rfl

theorem colMat_id6 : colMat id6 = 1 := by
  decide

theorem vecOf_xor (v w : ℕ) : vecOf (v ^^^ w) = vecOf v + vecOf w := by
  ext i
  simp only [vecOf, Nat.testBit_xor, bit2_xor, Pi.add_apply]

theorem vecOf_zero : vecOf 0 = 0 := by
  ext i
  simp [vecOf, bit2]

theorem vecOf_injective {v w : ℕ} (hv : v < 64) (hw : w < 64) (h : vecOf v = vecOf w) :
    v = w := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < 6
  · exact bit2_injective (congrFun h ⟨j, hj⟩)
  · have h2 : 64 ≤ 2 ^ j := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj)
    rw [Nat.testBit_eq_false_of_lt (hv.trans_le h2), Nat.testBit_eq_false_of_lt (hw.trans_le h2)]

theorem exists_vecOf (w : Fin 6 → ZMod 2) : ∃ v < 64, vecOf v = w := by
  classical
  have hinj : Set.InjOn vecOf (Finset.range 64 : Set ℕ) := fun v hv w hw h =>
    vecOf_injective (Finset.mem_range.1 hv) (Finset.mem_range.1 hw) h
  have hcard : ((Finset.range 64).image vecOf).card = (Finset.univ : Finset (Fin 6 → ZMod 2)).card
      := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_univ, Fintype.card_pi]
    simp
  have heq := Finset.eq_univ_of_card _ hcard
  have hw : w ∈ (Finset.range 64).image vecOf := by rw [heq]; exact Finset.mem_univ w
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  exact ⟨v, Finset.mem_range.1 hv, rfl⟩

theorem forall_vecOf {P : (Fin 6 → ZMod 2) → Prop} (h : ∀ v < 64, P (vecOf v))
    (w : Fin 6 → ZMod 2) : P w := by
  obtain ⟨v, hv, rfl⟩ := exists_vecOf w
  exact h v hv

@[expose] def canon6 (m : List ℕ) : Bool :=
  m.length == 6 && m.all (· < 64)

theorem colMat_injective {m m' : List ℕ} (h : canon6 m = true) (h' : canon6 m' = true)
    (e : colMat m = colMat m') : m = m' := by
  simp only [canon6, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h h'
  refine List.ext_getElem (h.1.trans h'.1.symm) fun j hj hj' => Nat.eq_of_testBit_eq fun i => ?_
  have hj6 : j < 6 := h.1 ▸ hj
  by_cases hi : i < 6
  · have := congrFun (congrFun e ⟨i, hi⟩) ⟨j, hj6⟩
    simp only [colMat, Matrix.of_apply, List.getD_eq_getElem _ _ hj,
      List.getD_eq_getElem _ _ hj'] at this
    exact bit2_injective this
  · have h2 : 64 ≤ 2 ^ i := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi)
    rw [Nat.testBit_eq_false_of_lt ((h.2 _ (List.getElem_mem hj)).trans_le h2),
      Nat.testBit_eq_false_of_lt ((h'.2 _ (List.getElem_mem hj')).trans_le h2)]

end CFSG.Quasithin.H13.U3
