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

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem r116b_inv_left {G : Type*} [Group G] {a b c : G} (ha : Commute a c)
    (h : a * b = b * a * c) : a⁻¹ * b = b * a⁻¹ * c⁻¹ := by
  have h1 : a * b * a⁻¹ = b * c := by
    calc a * b * a⁻¹ = b * a * c * a⁻¹ := by rw [h]
      _ = b * (a * c) * a⁻¹ := by simp only [mul_assoc]
      _ = b * (c * a) * a⁻¹ := by rw [ha.eq]
      _ = b * c := by group
  calc a⁻¹ * b = a⁻¹ * (b * c) * c⁻¹ := by group
    _ = a⁻¹ * (a * b * a⁻¹) * c⁻¹ := by rw [h1]
    _ = b * a⁻¹ * c⁻¹ := by group

theorem r116b_inv_right {G : Type*} [Group G] {a b c : G} (hb : Commute b c)
    (h : a * b = b * a * c) : a * b⁻¹ = b⁻¹ * a * c⁻¹ := by
  have h2 : b * a = a * b * c⁻¹ := by
    rw [h]
    group
  calc a * b⁻¹ = b⁻¹ * (b * a) * b⁻¹ := by group
    _ = b⁻¹ * (a * b * c⁻¹) * b⁻¹ := by rw [h2]
    _ = b⁻¹ * a * (b * c⁻¹) * b⁻¹ := by simp only [mul_assoc]
    _ = b⁻¹ * a * (c⁻¹ * b) * b⁻¹ := by rw [hb.inv_right.eq]
    _ = b⁻¹ * a * c⁻¹ := by group

theorem r116b_inv_pow_three {G : Type*} [Group G] (c : G) (hc : c ^ 3 = 1) (k : ℕ) :
    (c ^ k)⁻¹ = c ^ (2 * k) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hc, one_pow]

theorem r116b_pow_three_pow {G : Type*} [Group G] (c : G) (hc : c ^ 3 = 1) (k : ℕ) :
    (c ^ k) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hc, one_pow]

theorem r116b_mul_left_step {G : Type*} [Group G] {x y w c1 c2 : G} (hc1 : Commute c1 y)
    (h1 : x * w = w * x * c1) (h2 : y * w = w * y * c2) :
    x * y * w = w * (x * y) * (c1 * c2) := by
  calc x * y * w = x * (y * w) := by rw [mul_assoc]
    _ = x * (w * y * c2) := by rw [h2]
    _ = x * w * y * c2 := by simp only [mul_assoc]
    _ = w * x * c1 * y * c2 := by rw [h1]
    _ = w * x * (c1 * y) * c2 := by simp only [mul_assoc]
    _ = w * x * (y * c1) * c2 := by rw [hc1.eq]
    _ = w * (x * y) * (c1 * c2) := by simp only [mul_assoc]

theorem r116b_mul_right_step {G : Type*} [Group G] {x u v c1 c2 : G} (hc1 : Commute c1 v)
    (h1 : x * u = u * x * c1) (h2 : x * v = v * x * c2) :
    x * (u * v) = u * v * x * (c2 * c1) := by
  calc x * (u * v) = x * u * v := by rw [mul_assoc]
    _ = u * x * c1 * v := by rw [h1]
    _ = u * x * (c1 * v) := by simp only [mul_assoc]
    _ = u * x * (v * c1) := by rw [hc1.eq]
    _ = u * (x * v) * c1 := by simp only [mul_assoc]
    _ = u * (v * x * c2) * c1 := by rw [h2]
    _ = u * v * x * (c2 * c1) := by simp only [mul_assoc]

theorem r116b_cube_aux {G : Type*} [Group G] {u v e : G} (hA : v * u = u * v * e)
    (hEu : e * u = u * e) (hEv : e * v = v * e) : (u * v) ^ 3 = u ^ 3 * v ^ 3 * e ^ 3 := by
  have hcEv : Commute e v := hEv
  have hsq : (u * v) ^ 2 = u ^ 2 * v ^ 2 * e := by
    calc (u * v) ^ 2 = u * (v * u) * v := by simp only [pow_two, mul_assoc]
      _ = u * (u * v * e) * v := by rw [hA]
      _ = u * u * v * (e * v) := by simp only [mul_assoc]
      _ = u * u * v * (v * e) := by rw [hEv]
      _ = u ^ 2 * v ^ 2 * e := by simp only [pow_two, mul_assoc]
  have hv2u : v ^ 2 * u = u * v ^ 2 * e ^ 2 := by
    calc v ^ 2 * u = v * (v * u) := by simp only [pow_two, mul_assoc]
      _ = v * (u * v * e) := by rw [hA]
      _ = v * u * v * e := by simp only [mul_assoc]
      _ = u * v * e * v * e := by rw [hA]
      _ = u * v * (e * v) * e := by simp only [mul_assoc]
      _ = u * v * (v * e) * e := by rw [hEv]
      _ = u * v ^ 2 * e ^ 2 := by simp only [pow_two, mul_assoc]
  have hevu : e * (u * v) = u * v * e := by
    calc e * (u * v) = e * u * v := by rw [mul_assoc]
      _ = u * e * v := by rw [hEu]
      _ = u * (e * v) := by rw [mul_assoc]
      _ = u * (v * e) := by rw [hEv]
      _ = u * v * e := by rw [mul_assoc]
  have hEv2 : e ^ 2 * v = v * e ^ 2 := (hcEv.pow_left 2).eq
  have hcube2 : (u * v) ^ 3 = (u * v) ^ 2 * (u * v) := pow_succ (u * v) 2
  rw [hcube2, hsq]
  calc u ^ 2 * v ^ 2 * e * (u * v) = u ^ 2 * v ^ 2 * (e * (u * v)) := by simp only [mul_assoc]
    _ = u ^ 2 * v ^ 2 * (u * v * e) := by rw [hevu]
    _ = u ^ 2 * (v ^ 2 * u) * v * e := by simp only [mul_assoc]
    _ = u ^ 2 * (u * v ^ 2 * e ^ 2) * v * e := by rw [hv2u]
    _ = u ^ 3 * v ^ 2 * (e ^ 2 * v) * e := by group
    _ = u ^ 3 * v ^ 2 * (v * e ^ 2) * e := by rw [hEv2]
    _ = u ^ 3 * v ^ 3 * e ^ 3 := by group

theorem r116b_cube {G : Type*} [Group G] {u v c : G} (hcu : Commute c u) (hcv : Commute c v)
    (h : u * v = v * u * c) : (u * v) ^ 3 = u ^ 3 * v ^ 3 * (c ^ 3)⁻¹ := by
  have hA : v * u = u * v * c⁻¹ := by
    rw [h]
    group
  have hEu : c⁻¹ * u = u * c⁻¹ := hcu.inv_left.eq
  have hEv : c⁻¹ * v = v * c⁻¹ := hcv.inv_left.eq
  rw [r116b_cube_aux hA hEu hEv, inv_pow]

theorem isPGroup_closure_heisenberg {G : Type*} [Group G] [Finite G] {d P z : G}
    (hd : d ^ 3 = 1) (hP : P ^ 3 = 1) (hz : z ^ 3 = 1)
    (hzd : z * d = d * z) (hzP : z * P = P * z) (hdP : d * P = P * d * z) :
    IsPGroup 3 (Subgroup.closure ({d, P, z} : Set G)) := by
  have hA : ∀ g ∈ Subgroup.closure ({d, P, z} : Set G), Commute z g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hzd
      · exact hzP
      · exact Commute.refl _
    | one => exact Commute.one_right _
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  have hPd : P * d = d * P * z ^ 2 := by
    calc P * d = P * d * z ^ 3 := by rw [hz, mul_one]
      _ = P * d * z * z ^ 2 := by group
      _ = d * P * z ^ 2 := by rw [← hdP]
  have hB : ∀ g ∈ Subgroup.closure ({d, P, z} : Set G),
      ∀ h ∈ Subgroup.closure ({d, P, z} : Set G), ∃ k : ℕ, g * h = h * g * z ^ k := by
    intro g hg h hh
    refine Subgroup.closure_induction₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hg hh
    · intro x y hx hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by rw [pow_one]; exact hdP⟩
      · exact ⟨0, by rw [pow_zero, mul_one]; exact hzd.symm⟩
      · exact ⟨2, hPd⟩
      · exact ⟨0, by simp⟩
      · exact ⟨0, by rw [pow_zero, mul_one]; exact hzP.symm⟩
      · exact ⟨0, by rw [pow_zero, mul_one]; exact hzd⟩
      · exact ⟨0, by rw [pow_zero, mul_one]; exact hzP⟩
      · exact ⟨0, by simp⟩
    · intro x _
      exact ⟨0, by simp⟩
    · intro x _
      exact ⟨0, by simp⟩
    · intro x y w hx hy hw ih1 ih2
      obtain ⟨k1, h1⟩ := ih1
      obtain ⟨k2, h2⟩ := ih2
      exact ⟨k1 + k2, by rw [r116b_mul_left_step ((hA y hy).pow_left k1) h1 h2, pow_add]⟩
    · intro u v x hu hv hx ih1 ih2
      obtain ⟨k1, h1⟩ := ih1
      obtain ⟨k2, h2⟩ := ih2
      exact ⟨k2 + k1, by rw [r116b_mul_right_step ((hA v hv).pow_left k1) h1 h2, pow_add]⟩
    · intro x y hx hy ih
      obtain ⟨k, hk⟩ := ih
      exact ⟨2 * k, by rw [r116b_inv_left ((hA x hx).symm.pow_right k) hk,
        r116b_inv_pow_three z hz k]⟩
    · intro x y hx hy ih
      obtain ⟨k, hk⟩ := ih
      exact ⟨2 * k, by rw [r116b_inv_right ((hA y hy).symm.pow_right k) hk,
        r116b_inv_pow_three z hz k]⟩
  have hcube : ∀ g ∈ Subgroup.closure ({d, P, z} : Set G), g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hd
      · exact hP
      · exact hz
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      obtain ⟨k, hk⟩ := hB x hx y hy
      rw [r116b_cube ((hA x hx).pow_left k) ((hA y hy).pow_left k) hk, ihx, ihy,
        r116b_pow_three_pow z hz k]
      simp
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  refine isPGroup_iff_pow_pow_eq_one.mpr fun g => ⟨1, ?_⟩
  exact Subtype.ext (by simpa using hcube g.1 g.2)

open scoped Pointwise in
theorem exists_noncomm_in_sylow_of_isPGroup {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsPGroup 3 H) {x y : G} (hx : x ∈ H) (hy : y ∈ H) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y ≠ y * x) (S : Sylow 3 G) :
    ∃ x' ∈ (S : Subgroup G), ∃ y' ∈ (S : Subgroup G), x' ^ 3 = 1 ∧ y' ^ 3 = 1 ∧ x' * y' ≠ y' * x' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Sylow 3 G) :=
    Finite.of_injective (fun P : Sylow 3 G => ((P : Subgroup G) : Set G))
      (fun P Q h => Sylow.ext (SetLike.coe_injective h))
  obtain ⟨Q, hHQ⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  have hSQ : (S : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hconj : ∀ t ∈ (Q : Subgroup G), g * t * g⁻¹ ∈ (S : Subgroup G) := by
    intro t ht
    rw [hSQ]
    exact smul_mem_pointwise_smul t (MulAut.conj g) (Q : Subgroup G) ht
  refine ⟨g * x * g⁻¹, hconj x (hHQ hx), g * y * g⁻¹, hconj y (hHQ hy), ?_, ?_, ?_⟩
  · rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  · rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  · intro h
    apply hxy
    have h2 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := h
        _ = g * (y * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

end CFSG.RankThree.PartTwo.Sec11
