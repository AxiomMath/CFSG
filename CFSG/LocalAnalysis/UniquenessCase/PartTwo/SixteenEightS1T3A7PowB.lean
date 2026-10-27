module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped Pointwise commutatorElement

private lemma s16t3_mul_central_mul {D : Type*} [Group D] {c : D} (hc : c ∈ center D)
    (a b : D) : a * c * b = a * b * c := by
  rw [mul_assoc, ← Subgroup.mem_center_iff.1 hc b, ← mul_assoc]

private lemma s16t3_mul_cube_of_central {D : Type*} [Group D] (x y : D)
    (hd : y⁻¹ * x⁻¹ * y * x ∈ center D) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 * (y⁻¹ * x⁻¹ * y * x) ^ 3 := by
  set d := y⁻¹ * x⁻¹ * y * x with hd_def
  have hyx : y * x = x * y * d := by rw [hd_def]; group
  calc (x * y) ^ 3 = x * (y * x) * (y * x) * y := by
        simp only [pow_succ, pow_zero, one_mul, ← mul_assoc]
    _ = x * (x * y * d) * (x * y * d) * y := by rw [hyx]
    _ = x * x * (y * x) * y * y * d * d := by
        simp only [← mul_assoc, s16t3_mul_central_mul hd]
    _ = x * x * (x * y * d) * y * y * d * d := by rw [hyx]
    _ = x ^ 3 * y ^ 3 * d ^ 3 := by
        simp only [← mul_assoc, s16t3_mul_central_mul hd, pow_succ, pow_zero, one_mul]

private lemma s16t3_comm_cube_of_central {D : Type*} [Group D] (x y : D)
    (hd : y⁻¹ * x⁻¹ * y * x ∈ center D) (hx : x ^ 3 = 1) :
    (y⁻¹ * x⁻¹ * y * x) ^ 3 = 1 := by
  set d := y⁻¹ * x⁻¹ * y * x with hd_def
  have hconj : x⁻¹ * y * x = y * d := by rw [hd_def]; group
  have hk : ∀ k : ℕ, (x ^ k)⁻¹ * y * x ^ k = y * d ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hdk : d ^ k ∈ center D := Subgroup.pow_mem _ hd k
      calc (x ^ (k + 1))⁻¹ * y * x ^ (k + 1) = x⁻¹ * ((x ^ k)⁻¹ * y * x ^ k) * x := by
            group
        _ = x⁻¹ * (y * d ^ k) * x := by rw [ih]
        _ = x⁻¹ * y * x * d ^ k := by
            simp only [← mul_assoc, s16t3_mul_central_mul hdk]
        _ = y * d ^ (k + 1) := by rw [hconj]; group
  have h3 := hk 3
  rw [hx, inv_one, one_mul, mul_one] at h3
  exact (mul_eq_left.1 h3.symm)

private lemma s16t3_commutator_mem_of_generators {D : Type*} [Group D] (Z : Subgroup D)
    (hZc : Z ≤ center D) {a b : D} (hab : a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hgen : Subgroup.closure {a, b} ⊔ Z = ⊤) :
    ∀ x y : D, y⁻¹ * x⁻¹ * y * x ∈ Z := by
  classical
  haveI : Z.Normal := Subgroup.normal_of_le_center hZc
  have hmapZ : Subgroup.map (QuotientGroup.mk' Z) Z = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hcl : Subgroup.closure ({(a : D ⧸ Z), (b : D ⧸ Z)} : Set (D ⧸ Z)) = ⊤ := by
    have h1 : Subgroup.map (QuotientGroup.mk' Z)
        (Subgroup.closure ({a, b} : Set D) ⊔ Z) = ⊤ := by
      rw [hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)]
    rw [Subgroup.map_sup, hmapZ, MonoidHom.map_closure,
      show (QuotientGroup.mk' Z) '' ({a, b} : Set D)
        = ({(a : D ⧸ Z), (b : D ⧸ Z)} : Set (D ⧸ Z)) by simp, sup_bot_eq] at h1
    exact h1
  have hpair : ({(a : D ⧸ Z), (b : D ⧸ Z)} : Set (D ⧸ Z)).Pairwise Commute :=
    Set.pairwise_pair_of_symm_of_refl.mpr (by
      rw [← commutatorElement_eq_one_iff_commute]
      have h1 : ((a * b * a⁻¹ * b⁻¹ : D) : D ⧸ Z) = 1 :=
        (QuotientGroup.eq_one_iff (N := Z) (a * b * a⁻¹ * b⁻¹)).mpr hab
      simpa [commutatorElement_def] using h1)
  haveI hcommH : IsMulCommutative
      (Subgroup.closure ({(a : D ⧸ Z), (b : D ⧸ Z)} : Set (D ⧸ Z))) :=
    Subgroup.isMulCommutative_closure hpair
  have hcommQ : ∀ p q : D ⧸ Z, p * q = q * p := by
    intro p q
    have hp : p ∈ Subgroup.closure ({(a : D ⧸ Z), (b : D ⧸ Z)} : Set (D ⧸ Z)) := by
      rw [hcl]; exact Subgroup.mem_top p
    have hq : q ∈ Subgroup.closure ({(a : D ⧸ Z), (b : D ⧸ Z)} : Set (D ⧸ Z)) := by
      rw [hcl]; exact Subgroup.mem_top q
    exact Subtype.ext_iff.mp (hcommH.is_comm.comm ⟨p, hp⟩ ⟨q, hq⟩)
  intro x y
  rw [← QuotientGroup.eq_one_iff (N := Z) (y⁻¹ * x⁻¹ * y * x)]
  rw [show ((y⁻¹ * x⁻¹ * y * x : D) : D ⧸ Z) = ⁅(y : D ⧸ Z)⁻¹, (x : D ⧸ Z)⁻¹⁆ by
        rw [commutatorElement_def]; simp, commutatorElement_eq_one_iff_mul_comm]
  exact hcommQ _ _

theorem s16t3_pow_three_of_two_gen {D : Type*} [Group D] [Finite D] (Z : Subgroup D)
    (hZc : Z ≤ center D) (hZ3 : ∀ z ∈ Z, ∀ n : ℕ, z ^ 3 ^ n = 1 → z ^ 3 = 1) {a b : D}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hgen : Subgroup.closure {a, b} ⊔ Z = ⊤) {u : D} {n : ℕ} (hu : u ^ 3 ^ n = 1) :
    u ^ 3 = 1 := by
  classical
  haveI : Z.Normal := Subgroup.normal_of_le_center hZc
  have hab' : ∀ x y : D, y⁻¹ * x⁻¹ * y * x ∈ Z :=
    s16t3_commutator_mem_of_generators Z hZc hab hgen
  have hW : ∀ w ∈ Subgroup.closure ({a, b} : Set D), w ^ 3 = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => exact one_pow 3
    | mul x y _ _ hx hy =>
      rw [s16t3_mul_cube_of_central x y (hZc (hab' x y)), hx, hy,
        s16t3_comm_cube_of_central x y (hZc (hab' x y)) hx, one_mul, one_mul]
    | inv x _ hx => rw [inv_pow, hx, inv_one]
  have hu' : u ∈ Subgroup.closure ({a, b} : Set D) ⊔ Z := hgen ▸ Subgroup.mem_top u
  obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hu'
  have hcomm : Commute w z := (Subgroup.mem_center_iff.1 (hZc hz) w)
  have hcube : (w * z) ^ 3 = z ^ 3 := by rw [hcomm.mul_pow, hW w hw, one_mul]
  rw [hcube]
  refine hZ3 z hz (n + 1) ?_
  rw [pow_succ, pow_mul', ← hcube, ← pow_mul, ← pow_succ', pow_succ, pow_mul, hu, one_pow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
