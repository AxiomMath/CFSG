module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.Existence

@[expose] def schemeNeighbourMatrix : Fin 5 → Fin 5 → ℕ :=
  ![![0, 3968055, 0, 0, 0], ![1, 46134, 2097152, 1824768, 0], ![0, 3510, 837135, 3127410, 0],
    ![0, 648, 663552, 3295791, 8064], ![0, 0, 0, 3898440, 69615]]

section Scheme

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
private noncomputable def schemeMat (O : V → Fin 5 → Set V) (j : Fin 5) : Matrix V V ℤ :=
  Matrix.of fun v w => if w ∈ O v j then 1 else 0

private noncomputable def schemeLin (O : V → Fin 5 → Set V) : (Fin 5 → ℤ) →ₗ[ℤ] Matrix V V ℤ :=
  Fintype.linearCombination ℤ (schemeMat O)

private def schemeMul (M : Fin 5 → Fin 5 → ℕ) (c : Fin 5 → ℤ) : Fin 5 → ℤ :=
  fun l => ∑ k, (M l k : ℤ) * c k

omit [Fintype V] [DecidableEq V] in
private theorem schemeLin_apply (O : V → Fin 5 → Set V) (c : Fin 5 → ℤ) :
    schemeLin O c = ∑ k, c k • schemeMat O k := by
  simp [schemeLin, Fintype.linearCombination_apply]

omit [Fintype V] [DecidableEq V] in
private theorem schemeLin_single (O : V → Fin 5 → Set V) (j : Fin 5) :
    schemeLin O (Pi.single j 1) = schemeMat O j := by
  simp [schemeLin]

omit [DecidableEq V] in
private theorem schemeMat_mul_apply (O : V → Fin 5 → Set V)
    (hsymm : ∀ v w i, w ∈ O v i ↔ v ∈ O w i) (i j : Fin 5) (v w : V) :
    (schemeMat O i * schemeMat O j) v w = ((O v i ∩ O w j).ncard : ℤ) := by
  classical
  simp only [Matrix.mul_apply, schemeMat, Matrix.of_apply]
  have h : ∀ z, ((if z ∈ O v i then (1 : ℤ) else 0) * if w ∈ O z j then 1 else 0) =
      if z ∈ O v i ∩ O w j then 1 else 0 := by
    intro z
    rw [hsymm z w j]
    by_cases h1 : z ∈ O v i <;> by_cases h2 : z ∈ O w j <;> simp [h1, h2]
  simp_rw [h]
  rw [Finset.sum_boole, Set.ncard_eq_toFinset_card']
  congr 2
  ext z
  simp

omit [Fintype V] in
private theorem schemeMat_zero (O : V → Fin 5 → Set V) (hzero : ∀ v, O v 0 = {v}) :
    schemeMat O 0 = 1 := by
  ext v w
  simp [schemeMat, hzero, Matrix.one_apply, eq_comm]

section Counting

variable (O : V → Fin 5 → Set V) (M : Fin 5 → Fin 5 → ℕ)
  (hsymm : ∀ v w i, w ∈ O v i ↔ v ∈ O w i) (hpart : ∀ v w, ∃! i, w ∈ O v i)
  (hnbr : ∀ v i j, ∀ w ∈ O v i, (O w 1 ∩ O v j).ncard = M i j)

include hsymm hpart hnbr

omit [DecidableEq V] in
private theorem schemeMat_one_mul (j : Fin 5) :
    schemeMat O 1 * schemeMat O j = ∑ k, (M k j : ℤ) • schemeMat O k := by
  classical
  ext v w
  rw [schemeMat_mul_apply O hsymm]
  obtain ⟨k, hk, huniq⟩ := hpart v w
  rw [Matrix.sum_apply, Finset.sum_eq_single k]
  · simp [schemeMat, hk, hnbr w k j v ((hsymm v w k).1 hk)]
  · intro k' _ hk'
    have : w ∉ O v k' := fun h => hk' (huniq k' h)
    simp [schemeMat, this]
  · simp

private theorem schemeMat_one_mul_schemeLin (c : Fin 5 → ℤ) :
    schemeMat O 1 * schemeLin O c = schemeLin O (schemeMul M c) := by
  rw [schemeLin_apply, schemeLin_apply, Finset.mul_sum]
  simp only [mul_smul_comm, schemeMat_one_mul O M hsymm hpart hnbr, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [schemeMul, Finset.sum_smul]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]

private theorem schemeMat_one_pow_mul (n : ℕ) (c : Fin 5 → ℤ) :
    schemeMat O 1 ^ n * schemeLin O c = schemeLin O ((schemeMul M)^[n] c) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, schemeMat_one_mul_schemeLin O M hsymm hpart hnbr, ih,
      Function.iterate_succ_apply]

end Counting

private theorem schemeMul_iterates :
    (schemeMul schemeNeighbourMatrix)^[0] (Pi.single 0 1) = ![1, 0, 0, 0, 0] ∧
    (schemeMul schemeNeighbourMatrix)^[1] (Pi.single 0 1) = ![0, 1, 0, 0, 0] ∧
    (schemeMul schemeNeighbourMatrix)^[2] (Pi.single 0 1) = ![3968055, 46134, 3510, 648, 0] ∧
    (schemeMul schemeNeighbourMatrix)^[3] (Pi.single 0 1) =
      ![183062249370, 10675767195, 5126835870, 4494634920, 2526189120] ∧
    (schemeMul schemeNeighbourMatrix)^[4] (Pi.single 0 1) =
      ![42362031396955725, 19446118978164300, 18385891884044100, 18242588599038000,
        17697925213113600] ∧
    (schemeMul schemeNeighbourMatrix)^[0] (Pi.single 4 1) = ![0, 0, 0, 0, 1] ∧
    (schemeMul schemeNeighbourMatrix)^[1] (Pi.single 4 1) = ![0, 0, 0, 8064, 69615] ∧
    (schemeMul schemeNeighbourMatrix)^[2] (Pi.single 4 1) =
      ![0, 14714929152, 25219434240, 27138633984, 36283268385] ∧
    (schemeMul schemeNeighbourMatrix)^[3] (Pi.single 4 1) =
      ![58389648196239360, 103089556354498560, 106037355791727360, 106479795215928960,
        108324195997206735] ∧
    (schemeMul schemeNeighbourMatrix)^[4] (Pi.single 4 1) =
      ![409065029540249783500800, 421433367712419505766400, 422135402539760362252800,
        422236778613853186368000, 422646081765931641679425] := by
  have step : ∀ x y : Fin 5 → ℤ, (∀ i, ∑ k, (schemeNeighbourMatrix i k : ℤ) * x k = y i) →
      schemeMul schemeNeighbourMatrix x = y := fun x y h => funext h
  have e0 : (Pi.single 0 1 : Fin 5 → ℤ) = ![1, 0, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp
  have e4 : (Pi.single 4 1 : Fin 5 → ℤ) = ![0, 0, 0, 0, 1] := by
    funext i
    fin_cases i <;> simp
  have s1 := step ![1, 0, 0, 0, 0] ![0, 1, 0, 0, 0] (by
    intro i; fin_cases i <;> simp [schemeNeighbourMatrix, Fin.sum_univ_five])
  have s2 := step ![0, 1, 0, 0, 0] ![3968055, 46134, 3510, 648, 0] (by
    intro i; fin_cases i <;> simp [schemeNeighbourMatrix, Fin.sum_univ_five])
  have s3 := step ![3968055, 46134, 3510, 648, 0]
    ![183062249370, 10675767195, 5126835870, 4494634920, 2526189120] (by
    intro i; fin_cases i <;> simp [schemeNeighbourMatrix, Fin.sum_univ_five])
  have s4 := step ![183062249370, 10675767195, 5126835870, 4494634920, 2526189120]
    ![42362031396955725, 19446118978164300, 18385891884044100, 18242588599038000,
      17697925213113600] (by
    intro i; fin_cases i <;> simp [schemeNeighbourMatrix, Fin.sum_univ_five])
  have t1 := step ![0, 0, 0, 0, 1] ![0, 0, 0, 8064, 69615] (by
    intro i; fin_cases i <;> simp [schemeNeighbourMatrix, Fin.sum_univ_five])
  have t2 := step ![0, 0, 0, 8064, 69615]
    ![0, 14714929152, 25219434240, 27138633984, 36283268385] (by
    intro i; fin_cases i <;> simp [schemeNeighbourMatrix, Fin.sum_univ_five])
  have t3 := step ![0, 14714929152, 25219434240, 27138633984, 36283268385]
    ![58389648196239360, 103089556354498560, 106037355791727360, 106479795215928960,
      108324195997206735] (by
    intro i; fin_cases i <;> simp [schemeNeighbourMatrix, Fin.sum_univ_five])
  have t4 := step ![58389648196239360, 103089556354498560, 106037355791727360,
    106479795215928960, 108324195997206735]
    ![409065029540249783500800, 421433367712419505766400, 422135402539760362252800,
      422236778613853186368000, 422646081765931641679425] (by
    intro i; fin_cases i <;> simp [schemeNeighbourMatrix, Fin.sum_univ_five])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_zero_apply, e0]
  · rw [Function.iterate_one, e0, s1]
  · rw [Function.iterate_succ_apply', Function.iterate_one, e0, s1, s2]
  · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one, e0, s1,
      s2, s3]
  · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_one, e0, s1, s2, s3, s4]
  · rw [Function.iterate_zero_apply, e4]
  · rw [Function.iterate_one, e4, t1]
  · rw [Function.iterate_succ_apply', Function.iterate_one, e4, t1, t2]
  · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one, e4, t1,
      t2, t3]
  · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_one, e4, t1, t2, t3, t4]

theorem ncard_inter_four_of_neighbour_matrix {V : Type*} [Finite V] (O : V → Fin 5 → Set V)
    (hzero : ∀ v, O v 0 = {v}) (hsymm : ∀ v w i, w ∈ O v i ↔ v ∈ O w i)
    (hpart : ∀ v w, ∃! i, w ∈ O v i)
    (hnbr : ∀ v i j, ∀ w ∈ O v i, (O w 1 ∩ O v j).ncard = schemeNeighbourMatrix i j)
    (v w : V) (hw : w ∈ O v 2) : (O v 4 ∩ O w 4).ncard = 61776 := by
  classical
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨u0, u1, u2, u3, u4, w0, w1, w2, w3, w4⟩ := schemeMul_iterates
  set M := schemeNeighbourMatrix
  set P : Matrix V V ℤ :=
    (-208805604608289557334375 : ℤ) • schemeMat O 1 ^ 0 +
      (-1148833342527570238500 : ℤ) • schemeMat O 1 ^ 1 +
      (66491913010103550 : ℤ) • schemeMat O 1 ^ 2 + (-318249959220 : ℤ) • schemeMat O 1 ^ 3 +
      (76049 : ℤ) • schemeMat O 1 ^ 4 with hPdef
  have hP : ∀ x : Fin 5 → ℤ, P * schemeLin O x =
      schemeLin O ((-208805604608289557334375 : ℤ) • (schemeMul M)^[0] x +
        (-1148833342527570238500 : ℤ) • (schemeMul M)^[1] x +
        (66491913010103550 : ℤ) • (schemeMul M)^[2] x +
        (-318249959220 : ℤ) • (schemeMul M)^[3] x + (76049 : ℤ) • (schemeMul M)^[4] x) := by
    intro x
    simp only [hPdef, add_mul, smul_mul_assoc, schemeMat_one_pow_mul O M hsymm hpart hnbr,
      map_add, map_smul]
  have hP0 : P = (541949930110068480000 : ℤ) • schemeMat O 4 := by
    have h := hP (Pi.single 0 1)
    rw [schemeLin_single, schemeMat_zero O hzero, mul_one] at h
    rw [h, u0, u1, u2, u3, u4, ← schemeLin_single O 4, ← map_smul]
    congr 1
    funext i
    fin_cases i <;> simp
  have hP4 : P * schemeMat O 4 =
      schemeLin O ((541949930110068480000 : ℤ) • ![23113728, 405504, 61776, 34560, 0]) := by
    have h := hP (Pi.single 4 1)
    rw [schemeLin_single] at h
    rw [h, w0, w1, w2, w3, w4]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hP0, smul_mul_assoc, map_smul] at hP4
  have hent := congrArg (fun X : Matrix V V ℤ => X v w) hP4
  simp only [Matrix.smul_apply, smul_eq_mul] at hent
  rw [schemeMat_mul_apply O hsymm] at hent
  have hlin : schemeLin O (![23113728, 405504, 61776, 34560, 0] : Fin 5 → ℤ) v w = 61776 := by
    rw [schemeLin_apply, Matrix.sum_apply, Finset.sum_eq_single 2]
    · simp [schemeMat, hw]
    · intro k' _ hk'
      have : w ∉ O v k' := fun h => hk' ((hpart v w).unique h hw)
      simp [schemeMat, this]
    · simp
  rw [hlin] at hent
  have := mul_left_cancel₀ (by norm_num : (541949930110068480000 : ℤ) ≠ 0) hent
  exact_mod_cast this

end Scheme

end CFSG.Monster.Existence
