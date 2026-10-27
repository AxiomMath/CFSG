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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

theorem commutator_alg {R : Type*} [Ring R] (h2 : ∀ x : R, x + x = 0) {a b c : R}
    (haa : a * a = 0) (hbb : b * b = 0) (haba : a * b * a = 0) (hbab : b * a * b = 0)
    (hc : a * b + b * a = c) :
    (1 + a) * (1 + b) * (1 + a) * (1 + b) = 1 + c := by
  have hu : (1 + a) * (1 + b) * (1 + a) * (1 + b)
      = 1 + ((a + b + a * b) + (a + b + a * b)) + (a + b + a * b) * (a + b + a * b) := by
    noncomm_ring
  have hexp : (a + b + a * b) * (a + b + a * b)
      = a * a + a * b + a * (a * b) + b * a + b * b + b * (a * b) + a * b * a + a * b * b
        + a * b * (a * b) := by
    noncomm_ring
  have m1 : a * (a * b) = 0 := by rw [← mul_assoc, haa, zero_mul]
  have m2 : b * (a * b) = 0 := by rw [← mul_assoc]; exact hbab
  have m3 : a * b * b = 0 := by rw [mul_assoc, hbb, mul_zero]
  have m4 : a * b * (a * b) = 0 := by rw [← mul_assoc (a * b) a b, haba, zero_mul]
  rw [hu, h2 (a + b + a * b), add_zero, hexp, haa, m1, hbb, m2, haba, m3, m4, ← hc]
  abel

theorem sl2_torus_conj {K A : Type*} [Field K] [CharP K 2] [Ring A] [Algebra K A] {X Y : A}
    (hxx : X * X = 0) (hyy : Y * Y = 0) (hxyx : X * Y * X = X) (hyxy : Y * X * Y = Y)
    {c : K} (hc : c ≠ 0) (s : K) :
    ((1 + c • X) * (1 + c⁻¹ • Y) * (1 + c • X) * ((1 + (1 : K) • X) * (1 + (1 : K)⁻¹ • Y) * (1 + (1 : K) • X))) *
        (1 + s • X) =
      (1 + (c ^ 2 * s) • X) *
        ((1 + c • X) * (1 + c⁻¹ • Y) * (1 + c • X) * ((1 + (1 : K) • X) * (1 + (1 : K)⁻¹ • Y) * (1 + (1 : K) • X))) := by
  have hA2 : ∀ x : A, x + x = 0 := by
    intro x
    have h0 : (2 : K) • x = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    rwa [two_smul] at h0
  have hcan1 : ∀ u v : A, u + v + u = v := by
    intro u v
    rw [show u + v + u = v + (u + u) by abel, hA2, add_zero]
  have hcan2 : ∀ u v : A, u + (v + u) = v := by
    intro u v
    rw [show u + (v + u) = v + (u + u) by abel, hA2, add_zero]
  have hcan4 : ∀ u v : A, u + (u + v) = v := by
    intro u v
    rw [show u + (u + v) = v + (u + u) by abel, hA2, add_zero]
  have hcan5 : ∀ u v : A, v + u + u = v := by
    intro u v
    rw [add_assoc, hA2, add_zero]
  have hXXY : X * (X * Y) = 0 := by rw [← mul_assoc, hxx, zero_mul]
  have hYYX : Y * (Y * X) = 0 := by rw [← mul_assoc, hyy, zero_mul]
  have hXYX' : X * (Y * X) = X := by rw [← mul_assoc, hxyx]
  have hYXY' : Y * (X * Y) = Y := by rw [← mul_assoc, hyxy]
  have probeA : ∀ t : K, t ≠ 0 → (1 + t • X) * (1 + t⁻¹ • Y) * (1 + t • X) * X = t⁻¹ • (Y * X) := by
    intro t ht
    simp only [mul_assoc, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      smul_smul, hxx, hyy, hXYX', hYXY', hXXY, hYYX, smul_zero, smul_add, add_zero, zero_add,
      mul_zero, zero_mul, one_smul, hA2, hcan1, hcan2, hcan4, hcan5, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht]
    done
  have probeB : ∀ t : K, t ≠ 0 → (1 + t • X) * (1 + t⁻¹ • Y) * (1 + t • X) * (Y * X) = t • X := by
    intro t ht
    simp only [mul_assoc, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      smul_smul, hxx, hyy, hXYX', hYXY', hXXY, hYYX, smul_zero, smul_add, add_zero, zero_add,
      mul_zero, zero_mul, one_smul, hA2, hcan1, hcan2, hcan4, hcan5, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht]
    done
  have probeC : ∀ t : K, t ≠ 0 → X * ((1 + t • X) * (1 + t⁻¹ • Y) * (1 + t • X)) = t⁻¹ • (X * Y) := by
    intro t ht
    simp only [mul_assoc, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      smul_smul, hxx, hyy, hXYX', hYXY', hXXY, hYYX, smul_zero, smul_add, add_zero, zero_add,
      mul_zero, zero_mul, one_smul, hA2, hcan1, hcan2, hcan4, hcan5, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht]
    done
  have probeD : ∀ t : K, t ≠ 0 → X * Y * ((1 + t • X) * (1 + t⁻¹ • Y) * (1 + t • X)) = t • X := by
    intro t ht
    simp only [mul_assoc, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      smul_smul, hxx, hyy, hXYX', hYXY', hXXY, hYYX, smul_zero, smul_add, add_zero, zero_add,
      mul_zero, zero_mul, one_smul, hA2, hcan1, hcan2, hcan4, hcan5, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht]
    done
  have key : ∀ W V : A, V * X = Y * X → W * (Y * X) = c • X → X * W = c⁻¹ • (X * Y) →
      X * Y * V = X → W * V * (1 + s • X) = (1 + (c ^ 2 * s) • X) * (W * V) := by
    intro W V hVX hWYX hXW hXYV
    have hWVX : W * V * X = c • X := by rw [mul_assoc, hVX, hWYX]
    have hXWV : X * (W * V) = c⁻¹ • X := by rw [← mul_assoc, hXW, smul_mul_assoc, hXYV]
    have hsc : c ^ 2 * s * c⁻¹ = s * c := by
      calc c ^ 2 * s * c⁻¹ = s * c * (c * c⁻¹) := by ring
        _ = s * c := by rw [mul_inv_cancel₀ hc, mul_one]
    rw [mul_add, mul_one, mul_smul_comm, hWVX, add_mul, one_mul, smul_mul_assoc, hXWV,
      smul_smul, smul_smul, hsc]
  have hVX : (1 + (1 : K) • X) * (1 + (1 : K)⁻¹ • Y) * (1 + (1 : K) • X) * X = Y * X := by
    rw [probeA 1 one_ne_zero, inv_one, one_smul]
  have hXYV : X * Y * ((1 + (1 : K) • X) * (1 + (1 : K)⁻¹ • Y) * (1 + (1 : K) • X)) = X := by
    rw [probeD 1 one_ne_zero, one_smul]
  exact key _ _ hVX (probeB c hc) (probeC c hc) hXYV

theorem exists_ne_zero_one {K : Type*} [Field K] [Finite K] (h : 4 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra hne
  push Not at hne
  let f : Bool → K := fun b => cond b 1 0
  have hf : Function.Surjective f := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [f, hx]⟩
    · exact ⟨true, by simp [f, hne x hx]⟩
  have hle : Nat.card K ≤ Nat.card Bool := Nat.card_le_card_of_surjective f hf
  have hB : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  omega

theorem sq_add_one_ne_zero {K : Type*} [Field K] [CharP K 2] {c : K} (hc : c ≠ 1) : c ^ 2 + 1 ≠ 0 := by
  intro h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (c + 1) ^ 2 = 0 := by linear_combination h + c * h2
  have h3 : c + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
  exact hc (by linear_combination h3 - h2)

theorem three_distinct_of_filter_length {α : Type*} [DecidableEq α] {S : List α} (hS : S.Nodup) (p : α → Bool)
    (h : (S.filter p).length ≤ 2) {x y z : α} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hpx : p x = true) (hpy : p y = true) (hpz : p z = true) : x = y ∨ x = z ∨ y = z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hxy, hxz, hyz⟩ := hcon
  have hT : (S.filter p).Nodup := List.Nodup.filter p hS
  have hxT : x ∈ S.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
  have hyT : y ∈ S.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
  have hzT : z ∈ S.filter p := List.mem_filter.mpr ⟨hz, hpz⟩
  have hsub : ({x, y, z} : Finset α) ⊆ (S.filter p).toFinset := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hw
    rw [List.mem_toFinset]
    rcases hw with rfl | rfl | rfl
    · exact hxT
    · exact hyT
    · exact hzT
  have hc3 : ({x, y, z} : Finset α).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hlen : (S.filter p).toFinset.card = (S.filter p).length :=
    List.toFinset_card_of_nodup hT
  have hle := Finset.card_le_card hsub
  omega

end CFSG.RankThree.GF2n.Smith81.MinuscT
