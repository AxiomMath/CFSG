module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Ring.GeomSum

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item223CensusResProof

open Finset

@[expose] def cyc7 {R : Type*} [Semiring R] (t : R) : R :=
  ∑ k ∈ range 7, t ^ k

@[expose] def remSeq {K : Type*} [CommRing K] (a b : K) : ℕ → K × K
  | 0 => (0, 1)
  | k + 1 => ((remSeq a b k).2 - a * (remSeq a b k).1, -b * (remSeq a b k).1)

@[expose] def cycRem {K : Type*} [CommRing K] (a b : K) : K × K :=
  ∑ k ∈ range 7, remSeq a b k

theorem cyc7_mul_sub_one {R : Type*} [Ring R] (t : R) : cyc7 t * (t - 1) = t ^ 7 - 1 :=
  geom_sum_mul t 7

theorem sub_one_mul_cyc7 {R : Type*} [Ring R] (t : R) : (t - 1) * cyc7 t = t ^ 7 - 1 :=
  mul_geom_sum t 7

theorem commute_cyc7 {R : Type*} [Semiring R] {s t : R} (h : Commute s t) :
    Commute s (cyc7 t) :=
  Commute.sum_right _ _ _ fun k _ => h.pow_right k

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem pow_apply_of_fixed {c : Module.End K V} {v : V} (hv : c v = v) (k : ℕ) :
    (c ^ k) v = v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, hv]

theorem cyc7_apply_of_fixed {c : Module.End K V} {v : V} (hv : c v = v) :
    (cyc7 c) v = (7 : K) • v := by
  rw [cyc7, LinearMap.sum_apply]
  simp only [pow_apply_of_fixed hv, sum_const, card_range]
  rw [← Nat.cast_smul_eq_nsmul K]
  norm_num

theorem pow_apply_of_eigen {c : Module.End K V} {v : V} {t : K} (hv : c v = t • v) (k : ℕ) :
    (c ^ k) v = t ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, ← pow_succ]

theorem cyc7_apply_of_eigen {c : Module.End K V} {v : V} {t : K} (hv : c v = t • v) :
    (cyc7 c) v = cyc7 t • v := by
  rw [cyc7, LinearMap.sum_apply, cyc7, sum_smul]
  exact sum_congr rfl fun k _ => pow_apply_of_eigen hv k

theorem pow_apply_of_quadratic {c : Module.End K V} {v : V} {a b : K}
    (hv : c (c v) = -a • c v - b • v) (k : ℕ) :
    (c ^ k) v = (remSeq a b k).1 • c v + (remSeq a b k).2 • v := by
  induction k with
  | zero => simp [remSeq]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, map_smul, hv]
    simp only [remSeq, smul_sub, smul_smul, sub_smul, neg_mul, neg_smul]
    module

theorem cyc7_apply_of_quadratic {c : Module.End K V} {v : V} {a b : K}
    (hv : c (c v) = -a • c v - b • v) :
    (cyc7 c) v = (cycRem a b).1 • c v + (cycRem a b).2 • v := by
  rw [cyc7, LinearMap.sum_apply, cycRem, Prod.fst_sum, Prod.snd_sum, sum_smul, sum_smul,
    ← sum_add_distrib]
  exact sum_congr rfl fun k _ => pow_apply_of_quadratic hv k

theorem eq_zero_of_cyc7_mulVec (hP1 : ∀ t : K, cyc7 t ≠ 0) (hP2 : ∀ a b : K, cycRem a b ≠ 0)
    {c : Module.End K V} {v : V} (hv : (cyc7 c) v = 0) (hv0 : v ≠ 0) {r₀ r₁ r₂ : K}
    (h : r₀ • v + r₁ • c v + r₂ • c (c v) = 0) : r₀ = 0 ∧ r₁ = 0 ∧ r₂ = 0 := by
  have heigen : ∀ t : K, c v ≠ t • v := by
    intro t ht
    apply hP1 t
    have h1 := cyc7_apply_of_eigen ht
    rw [hv] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hv0
  by_cases hr₂ : r₂ = 0
  · subst hr₂
    rw [zero_smul, add_zero] at h
    by_cases hr₁ : r₁ = 0
    · subst hr₁
      rw [zero_smul, add_zero] at h
      exact ⟨(smul_eq_zero.mp h).resolve_right hv0, rfl, rfl⟩
    · exfalso
      apply heigen (-(r₀ / r₁))
      have h1 : r₁ • c v = -(r₀ • v) := eq_neg_of_add_eq_zero_right h
      calc c v = r₁⁻¹ • (r₁ • c v) := by rw [smul_smul, inv_mul_cancel₀ hr₁, one_smul]
        _ = -(r₀ / r₁) • v := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  · exfalso
    have hq : c (c v) = -(r₁ / r₂) • c v - (r₀ / r₂) • v := by
      have h1 : r₂ • c (c v) = -(r₀ • v + r₁ • c v) := eq_neg_of_add_eq_zero_right h
      calc c (c v) = r₂⁻¹ • (r₂ • c (c v)) := by
            rw [smul_smul, inv_mul_cancel₀ hr₂, one_smul]
        _ = -(r₁ / r₂) • c v - (r₀ / r₂) • v := by
            rw [h1, smul_neg, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul,
              neg_smul]
            abel
    have h1 := cyc7_apply_of_quadratic hq
    rw [hv] at h1
    set α := (cycRem (r₁ / r₂) (r₀ / r₂)).1
    set β := (cycRem (r₁ / r₂) (r₀ / r₂)).2
    by_cases hα : α = 0
    · rw [hα, zero_smul, zero_add] at h1
      have hβ : β = 0 := (smul_eq_zero.mp h1.symm).resolve_right hv0
      exact hP2 (r₁ / r₂) (r₀ / r₂) (Prod.ext hα hβ)
    · apply heigen (-(β / α))
      have h2 : α • c v = -(β • v) := eq_neg_of_add_eq_zero_left h1.symm
      calc c v = α⁻¹ • (α • c v) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
        _ = -(β / α) • v := by rw [h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

variable [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem exists_last_ne_zero {N : Module.End K V} (hN3 : N ^ 3 = 0) {y : V} (hy : N y ≠ 0) :
    ∃ y', (y' = y ∨ y' = N y) ∧ N y' ≠ 0 ∧ N (N y') = 0 := by
  by_cases h2 : N (N y) = 0
  · exact ⟨y, Or.inl rfl, hy, h2⟩
  · refine ⟨N y, Or.inr rfl, h2, ?_⟩
    have := congrArg (fun f : Module.End K V => f y) hN3
    simpa [pow_succ, Module.End.mul_apply] using this

theorem apply_eq_zero_of_cyc7 (hV : Module.finrank K V ≤ 4) (hP1 : ∀ t : K, cyc7 t ≠ 0)
    (hP2 : ∀ a b : K, cycRem a b ≠ 0) {c N : Module.End K V} (hNc : N * c = c * N)
    (hN3 : N ^ 3 = 0) {y : V} (hy : (cyc7 c) y = 0) : N y = 0 := by
  by_contra hNy
  have hcomm : Commute N (cyc7 c) := commute_cyc7 hNc
  obtain ⟨y', hy', hz, hNz⟩ := exists_last_ne_zero hN3 hNy
  have hNcv : ∀ w, N (c w) = c (N w) := fun w => by
    rw [← Module.End.mul_apply, hNc, Module.End.mul_apply]
  have hy'0 : (cyc7 c) y' = 0 := by
    rcases hy' with rfl | rfl
    · exact hy
    · rw [← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply, hy, map_zero]
  set z := N y'
  have hz0 : (cyc7 c) z = 0 := by
    rw [← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply, hy'0, map_zero]
  have hli : LinearIndependent K ![y', c y', c (c y'), z, c z, c (c z)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_six, Matrix.cons_val] at hg
    have hN := congrArg N hg
    simp only [map_add, map_smul, hNcv, hNz, map_zero, smul_zero, add_zero] at hN
    obtain ⟨h0, h1, h2⟩ := eq_zero_of_cyc7_mulVec hP1 hP2 hz0 hz hN
    rw [h0, h1, h2, zero_smul, zero_smul, zero_smul, zero_add, zero_add, zero_add] at hg
    obtain ⟨h3, h4, h5⟩ := eq_zero_of_cyc7_mulVec hP1 hP2 hz0 hz hg
    intro i
    fin_cases i <;> assumption
  have := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at this
  omega

theorem apply_eq_zero_of_fixed (hV : Module.finrank K V ≤ 4) (h7 : (7 : K) ≠ 0)
    (hP1 : ∀ t : K, cyc7 t ≠ 0) (hP2 : ∀ a b : K, cycRem a b ≠ 0) {c N : Module.End K V}
    (hNc : N * c = c * N) (hN3 : N ^ 3 = 0) {v₀ : V} (hv₀ : (cyc7 c) v₀ = 0) (hv₀0 : v₀ ≠ 0)
    {y : V} (hy : c y = y) : N y = 0 := by
  by_contra hNy
  obtain ⟨y', hy', hz, hNz⟩ := exists_last_ne_zero hN3 hNy
  have hNcv : ∀ w, N (c w) = c (N w) := fun w => by
    rw [← Module.End.mul_apply, hNc, Module.End.mul_apply]
  have hcy' : c y' = y' := by
    rcases hy' with rfl | rfl
    · exact hy
    · rw [← hNcv, hy]
  set z := N y'
  have hcz : c z = z := by rw [← hNcv, hcy']
  have hcomm : Commute c (cyc7 c) := commute_cyc7 (Commute.refl c)
  have hcv : ∀ w, (cyc7 c) (c w) = c ((cyc7 c) w) := fun w => by
    rw [← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply]
  have hli : LinearIndependent K ![y', z, v₀, c v₀, c (c v₀)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_five, Matrix.cons_val] at hg
    have hΦ := congrArg (fun w => (cyc7 c : Module.End K V) w) hg
    simp only [map_add, map_smul, hcv, hv₀, map_zero, smul_zero, add_zero,
      cyc7_apply_of_fixed hcy', cyc7_apply_of_fixed hcz, smul_smul] at hΦ
    have hyz : g 0 • y' + g 1 • z = 0 := by
      have h1 : (7 : K) • (g 0 • y' + g 1 • z) = 0 := by
        rw [smul_add, smul_smul, smul_smul, mul_comm (7 : K), mul_comm (7 : K)]
        exact hΦ
      exact (smul_eq_zero.mp h1).resolve_left h7
    have hN := congrArg N hyz
    simp only [map_add, map_smul, hNz, smul_zero, add_zero, map_zero] at hN
    have hg0 : g 0 = 0 := (smul_eq_zero.mp hN).resolve_right hz
    rw [hg0, zero_smul, zero_add] at hyz
    have hg1 : g 1 = 0 := (smul_eq_zero.mp hyz).resolve_right hz
    rw [hg0, hg1, zero_smul, zero_smul, zero_add, zero_add] at hg
    obtain ⟨h2, h3, h4⟩ := eq_zero_of_cyc7_mulVec hP1 hP2 hv₀ hv₀0 hg
    intro i
    fin_cases i <;> assumption
  have := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at this
  omega

theorem eq_zero_of_commute_cyc7 (hV : Module.finrank K V ≤ 4) (h7 : (7 : K) ≠ 0)
    (hP1 : ∀ t : K, cyc7 t ≠ 0) (hP2 : ∀ a b : K, cycRem a b ≠ 0) {c N : Module.End K V}
    (hc7 : c ^ 7 = 1) (hc1 : c ≠ 1) (hNc : N * c = c * N) (hN3 : N ^ 3 = 0) : N = 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, c x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hc1 (LinearMap.ext fun x => by rw [h x, Module.End.one_apply])
  set v₀ := c x₀ - x₀
  have hv₀0 : v₀ ≠ 0 := sub_ne_zero.mpr hx₀
  have hcyc : cyc7 c * (c - 1) = 0 := by rw [cyc7_mul_sub_one, hc7, sub_self]
  have hv₀ : (cyc7 c) v₀ = 0 := by
    have h1 : (cyc7 c * (c - 1)) x₀ = 0 := by rw [hcyc, LinearMap.zero_apply]
    rwa [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at h1
  have hfix : ∀ x, c ((cyc7 c) x) = (cyc7 c) x := by
    intro x
    have h1 : ((c - 1) * cyc7 c) x = 0 := by
      rw [sub_one_mul_cyc7, hc7, sub_self, LinearMap.zero_apply]
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at h1
    exact sub_eq_zero.mp h1
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply]
  have hdecomp : x = (7 : K)⁻¹ • (cyc7 c) x + (x - (7 : K)⁻¹ • (cyc7 c) x) := by abel
  have hker : (cyc7 c) (x - (7 : K)⁻¹ • (cyc7 c) x) = 0 := by
    rw [map_sub, map_smul, cyc7_apply_of_fixed (hfix x), smul_smul, inv_mul_cancel₀ h7, one_smul,
      sub_self]
  rw [hdecomp, map_add, map_smul,
    apply_eq_zero_of_fixed hV h7 hP1 hP2 hNc hN3 hv₀ hv₀0 (hfix x),
    apply_eq_zero_of_cyc7 hV hP1 hP2 hNc hN3 hker, smul_zero, add_zero]

end Item223CensusResProof

end CFSG.RankThree.PartTwo.Sec21
