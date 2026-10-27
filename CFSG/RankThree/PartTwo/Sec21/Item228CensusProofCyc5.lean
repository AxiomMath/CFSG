module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofSeven

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item228CensusProof

open Finset Item223CensusResProof

@[expose] def cyc5 {R : Type*} [Semiring R] (t : R) : R :=
  ∑ k ∈ range 5, t ^ k

@[expose] def cyc5Rem {K : Type*} [CommRing K] (a b : K) : K × K :=
  ∑ k ∈ range 5, remSeq a b k

theorem cyc5_mul_sub_one {R : Type*} [Ring R] (t : R) : cyc5 t * (t - 1) = t ^ 5 - 1 :=
  geom_sum_mul t 5

theorem sub_one_mul_cyc5 {R : Type*} [Ring R] (t : R) : (t - 1) * cyc5 t = t ^ 5 - 1 :=
  mul_geom_sum t 5

theorem commute_cyc5 {R : Type*} [Semiring R] {s t : R} (h : Commute s t) :
    Commute s (cyc5 t) :=
  Commute.sum_right _ _ _ fun k _ => h.pow_right k

theorem cyc5_eq {R : Type*} [Semiring R] (t : R) : cyc5 t = 1 + t + t ^ 2 + t ^ 3 + t ^ 4 := by
  simp [cyc5, Finset.sum_range_succ]

theorem cyc5Rem_eq {K : Type*} [CommRing K] (a b : K) :
    cyc5Rem a b = remSeq a b 0 + remSeq a b 1 + remSeq a b 2 + remSeq a b 3 + remSeq a b 4 := by
  simp [cyc5Rem, Finset.sum_range_succ]

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem cyc5_apply_of_fixed {c : Module.End K V} {v : V} (hv : c v = v) :
    (cyc5 c) v = (5 : K) • v := by
  rw [cyc5, LinearMap.sum_apply]
  simp only [pow_apply_of_fixed hv, sum_const, card_range]
  rw [← Nat.cast_smul_eq_nsmul K]
  norm_num

theorem cyc5_apply_of_eigen {c : Module.End K V} {v : V} {t : K} (hv : c v = t • v) :
    (cyc5 c) v = cyc5 t • v := by
  rw [cyc5, LinearMap.sum_apply, cyc5, sum_smul]
  exact sum_congr rfl fun k _ => pow_apply_of_eigen hv k

theorem cyc5_apply_of_quadratic {c : Module.End K V} {v : V} {a b : K}
    (hv : c (c v) = -a • c v - b • v) :
    (cyc5 c) v = (cyc5Rem a b).1 • c v + (cyc5Rem a b).2 • v := by
  rw [cyc5, LinearMap.sum_apply, cyc5Rem, Prod.fst_sum, Prod.snd_sum, sum_smul, sum_smul,
    ← sum_add_distrib]
  exact sum_congr rfl fun k _ => pow_apply_of_quadratic hv k

theorem ne_smul_of_cyc5 (hP1 : ∀ t : K, cyc5 t ≠ 0) {c : Module.End K V} {v : V}
    (hv : (cyc5 c) v = 0) (hv0 : v ≠ 0) (t : K) : c v ≠ t • v := by
  intro ht
  apply hP1 t
  have h1 := cyc5_apply_of_eigen ht
  rw [hv] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_right hv0

theorem eq_zero_of_cyc5_pair (hP1 : ∀ t : K, cyc5 t ≠ 0) {c : Module.End K V} {v : V}
    (hv : (cyc5 c) v = 0) (hv0 : v ≠ 0) {r₀ r₁ : K} (h : r₀ • v + r₁ • c v = 0) :
    r₀ = 0 ∧ r₁ = 0 := by
  by_cases hr₁ : r₁ = 0
  · subst hr₁
    rw [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right hv0, rfl⟩
  · exfalso
    apply ne_smul_of_cyc5 hP1 hv hv0 (-(r₀ / r₁))
    have h1 : r₁ • c v = -(r₀ • v) := eq_neg_of_add_eq_zero_right h
    calc c v = r₁⁻¹ • (r₁ • c v) := by rw [smul_smul, inv_mul_cancel₀ hr₁, one_smul]
      _ = -(r₀ / r₁) • v := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem eq_zero_of_cyc5_triple (hP1 : ∀ t : K, cyc5 t ≠ 0) (hP2 : ∀ a b : K, cyc5Rem a b ≠ 0)
    {c : Module.End K V} {v : V} (hv : (cyc5 c) v = 0) (hv0 : v ≠ 0) {r₀ r₁ r₂ : K}
    (h : r₀ • v + r₁ • c v + r₂ • c (c v) = 0) : r₀ = 0 ∧ r₁ = 0 ∧ r₂ = 0 := by
  by_cases hr₂ : r₂ = 0
  · subst hr₂
    rw [zero_smul, add_zero] at h
    obtain ⟨h0, h1⟩ := eq_zero_of_cyc5_pair hP1 hv hv0 h
    exact ⟨h0, h1, rfl⟩
  · exfalso
    have hq : c (c v) = -(r₁ / r₂) • c v - (r₀ / r₂) • v := by
      have h1 : r₂ • c (c v) = -(r₀ • v + r₁ • c v) := eq_neg_of_add_eq_zero_right h
      calc c (c v) = r₂⁻¹ • (r₂ • c (c v)) := by
            rw [smul_smul, inv_mul_cancel₀ hr₂, one_smul]
        _ = -(r₁ / r₂) • c v - (r₀ / r₂) • v := by
            rw [h1, smul_neg, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul,
              neg_smul]
            abel
    have h1 := cyc5_apply_of_quadratic hq
    rw [hv] at h1
    set α := (cyc5Rem (r₁ / r₂) (r₀ / r₂)).1
    set β := (cyc5Rem (r₁ / r₂) (r₀ / r₂)).2
    by_cases hα : α = 0
    · rw [hα, zero_smul, zero_add] at h1
      have hβ : β = 0 := (smul_eq_zero.mp h1.symm).resolve_right hv0
      exact hP2 (r₁ / r₂) (r₀ / r₂) (Prod.ext hα hβ)
    · apply ne_smul_of_cyc5 hP1 hv hv0 (-(β / α))
      have h2 : α • c v = -(β • v) := eq_neg_of_add_eq_zero_left h1.symm
      calc c v = α⁻¹ • (α • c v) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
        _ = -(β / α) • v := by rw [h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

variable [FiniteDimensional K V]

theorem apply_eq_zero_of_cyc5 (hP1 : ∀ t : K, cyc5 t ≠ 0)
    (hdim : Module.finrank K V ≤ 3 ∨ (Module.finrank K V ≤ 4 ∧ ∀ a b : K, cyc5Rem a b ≠ 0))
    {c N : Module.End K V} (hNc : N * c = c * N) (hN3 : N ^ 3 = 0) {y : V}
    (hy : (cyc5 c) y = 0) : N y = 0 := by
  by_contra hNy
  have hcomm : Commute N (cyc5 c) := commute_cyc5 hNc
  obtain ⟨y', hy', hz, hNz⟩ := exists_last_ne_zero hN3 hNy
  have hNcv : ∀ w, N (c w) = c (N w) := fun w => by
    rw [← Module.End.mul_apply, hNc, Module.End.mul_apply]
  have hy'0 : (cyc5 c) y' = 0 := by
    rcases hy' with rfl | rfl
    · exact hy
    · rw [← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply, hy, map_zero]
  set z := N y'
  have hz0 : (cyc5 c) z = 0 := by
    rw [← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply, hy'0, map_zero]
  rcases hdim with h3 | ⟨h4, hP2⟩
  · have hli : LinearIndependent K ![y', c y', z, c z] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_four, Matrix.cons_val] at hg
      have hN := congrArg N hg
      simp only [map_add, map_smul, hNcv, hNz, map_zero, smul_zero, add_zero] at hN
      obtain ⟨h0, h1⟩ := eq_zero_of_cyc5_pair hP1 hz0 hz hN
      rw [h0, h1, zero_smul, zero_smul, zero_add, zero_add] at hg
      obtain ⟨h2, h3'⟩ := eq_zero_of_cyc5_pair hP1 hz0 hz hg
      intro i
      fin_cases i <;> assumption
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega
  · have hli : LinearIndependent K ![y', c y', c (c y'), z, c z, c (c z)] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_six, Matrix.cons_val] at hg
      have hN := congrArg N hg
      simp only [map_add, map_smul, hNcv, hNz, map_zero, smul_zero, add_zero] at hN
      obtain ⟨h0, h1, h2⟩ := eq_zero_of_cyc5_triple hP1 hP2 hz0 hz hN
      rw [h0, h1, h2, zero_smul, zero_smul, zero_smul, zero_add, zero_add, zero_add] at hg
      obtain ⟨h3, h4', h5⟩ := eq_zero_of_cyc5_triple hP1 hP2 hz0 hz hg
      intro i
      fin_cases i <;> assumption
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega

theorem apply_eq_zero_of_fixed5 (h5 : (5 : K) ≠ 0) (hP1 : ∀ t : K, cyc5 t ≠ 0)
    (hdim : Module.finrank K V ≤ 3 ∨ (Module.finrank K V ≤ 4 ∧ ∀ a b : K, cyc5Rem a b ≠ 0))
    {c N : Module.End K V} (hNc : N * c = c * N) (hN3 : N ^ 3 = 0) {v₀ : V}
    (hv₀ : (cyc5 c) v₀ = 0) (hv₀0 : v₀ ≠ 0) {y : V} (hy : c y = y) : N y = 0 := by
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
  have hcomm : Commute c (cyc5 c) := commute_cyc5 (Commute.refl c)
  have hcv : ∀ w, (cyc5 c) (c w) = c ((cyc5 c) w) := fun w => by
    rw [← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply]
  have hpair : ∀ g₀ g₁ : K, g₀ • y' + g₁ • z = 0 → g₀ = 0 ∧ g₁ = 0 := by
    intro g₀ g₁ hyz
    have hN := congrArg N hyz
    simp only [map_add, map_smul, hNz, smul_zero, add_zero, map_zero] at hN
    have hg0 : g₀ = 0 := (smul_eq_zero.mp hN).resolve_right hz
    rw [hg0, zero_smul, zero_add] at hyz
    exact ⟨hg0, (smul_eq_zero.mp hyz).resolve_right hz⟩
  rcases hdim with h3 | ⟨h4, hP2⟩
  · have hli : LinearIndependent K ![y', z, v₀, c v₀] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_four, Matrix.cons_val] at hg
      have hΦ := congrArg (fun w => (cyc5 c : Module.End K V) w) hg
      simp only [map_add, map_smul, hcv, hv₀, map_zero, smul_zero, add_zero,
        cyc5_apply_of_fixed hcy', cyc5_apply_of_fixed hcz, smul_smul] at hΦ
      have hyz : g 0 • y' + g 1 • z = 0 := by
        have h1 : (5 : K) • (g 0 • y' + g 1 • z) = 0 := by
          rw [smul_add, smul_smul, smul_smul, mul_comm (5 : K), mul_comm (5 : K)]
          exact hΦ
        exact (smul_eq_zero.mp h1).resolve_left h5
      obtain ⟨hg0, hg1⟩ := hpair _ _ hyz
      rw [hg0, hg1, zero_smul, zero_smul, zero_add, zero_add] at hg
      obtain ⟨h2, h3'⟩ := eq_zero_of_cyc5_pair hP1 hv₀ hv₀0 hg
      intro i
      fin_cases i <;> assumption
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega
  · have hli : LinearIndependent K ![y', z, v₀, c v₀, c (c v₀)] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_five, Matrix.cons_val] at hg
      have hΦ := congrArg (fun w => (cyc5 c : Module.End K V) w) hg
      simp only [map_add, map_smul, hcv, hv₀, map_zero, smul_zero, add_zero,
        cyc5_apply_of_fixed hcy', cyc5_apply_of_fixed hcz, smul_smul] at hΦ
      have hyz : g 0 • y' + g 1 • z = 0 := by
        have h1 : (5 : K) • (g 0 • y' + g 1 • z) = 0 := by
          rw [smul_add, smul_smul, smul_smul, mul_comm (5 : K), mul_comm (5 : K)]
          exact hΦ
        exact (smul_eq_zero.mp h1).resolve_left h5
      obtain ⟨hg0, hg1⟩ := hpair _ _ hyz
      rw [hg0, hg1, zero_smul, zero_smul, zero_add, zero_add] at hg
      obtain ⟨h2, h3, h4'⟩ := eq_zero_of_cyc5_triple hP1 hP2 hv₀ hv₀0 hg
      intro i
      fin_cases i <;> assumption
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega

theorem eq_zero_of_commute_cyc5 (h5 : (5 : K) ≠ 0) (hP1 : ∀ t : K, cyc5 t ≠ 0)
    (hdim : Module.finrank K V ≤ 3 ∨ (Module.finrank K V ≤ 4 ∧ ∀ a b : K, cyc5Rem a b ≠ 0))
    {c N : Module.End K V} (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) (hNc : N * c = c * N)
    (hN3 : N ^ 3 = 0) : N = 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, c x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hc1 (LinearMap.ext fun x => by rw [h x, Module.End.one_apply])
  set v₀ := c x₀ - x₀
  have hv₀0 : v₀ ≠ 0 := sub_ne_zero.mpr hx₀
  have hcyc : cyc5 c * (c - 1) = 0 := by rw [cyc5_mul_sub_one, hc5, sub_self]
  have hv₀ : (cyc5 c) v₀ = 0 := by
    have h1 : (cyc5 c * (c - 1)) x₀ = 0 := by rw [hcyc, LinearMap.zero_apply]
    rwa [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at h1
  have hfix : ∀ x, c ((cyc5 c) x) = (cyc5 c) x := by
    intro x
    have h1 : ((c - 1) * cyc5 c) x = 0 := by
      rw [sub_one_mul_cyc5, hc5, sub_self, LinearMap.zero_apply]
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at h1
    exact sub_eq_zero.mp h1
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply]
  have hdecomp : x = (5 : K)⁻¹ • (cyc5 c) x + (x - (5 : K)⁻¹ • (cyc5 c) x) := by abel
  have hker : (cyc5 c) (x - (5 : K)⁻¹ • (cyc5 c) x) = 0 := by
    rw [map_sub, map_smul, cyc5_apply_of_fixed (hfix x), smul_smul, inv_mul_cancel₀ h5,
      one_smul, sub_self]
  rw [hdecomp, map_add, map_smul,
    apply_eq_zero_of_fixed5 h5 hP1 hdim hNc hN3 hv₀ hv₀0 (hfix x),
    apply_eq_zero_of_cyc5 hP1 hdim hNc hN3 hker, smul_zero, add_zero]

end Item228CensusProof

end CFSG.RankThree.PartTwo.Sec21
