module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

open Subgroup

private lemma owCo_polar_weightedSumSquares {K : Type*} [CommRing K] {d : ℕ}
    (w : Fin d → K) (x y : Fin d → K) :
    QuadraticMap.polar (QuadraticMap.weightedSumSquares K w) x y =
      2 * ∑ i, w i * (x i * y i) := by
  simp only [QuadraticMap.polar, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
    Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma owCo_quad_expand {K : Type*} [CommRing K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (x b : Fin d → K) (s : K) :
    Q (x + s • b) = Q x + (s * s) * Q b + s * QuadraticMap.polar Q x b := by
  rw [QuadraticMap.map_add Q x (s • b), QuadraticMap.map_smul Q s b,
    QuadraticMap.polar_smul_right Q s x b]
  simp only [smul_eq_mul]

private def owCo_isRefl {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (t : V ≃ₗ[K] V) : Prop :=
  t * t = 1 ∧ Module.finrank K (LinearMap.range ((t : V →ₗ[K] V) - LinearMap.id)) = 1

private def owCo_classRefl {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (c : K) : Set (V ≃ₗ[K] V) :=
  {t | owCo_isRefl t ∧ (∀ v, Q (t v) = Q v) ∧ ∃ a, Q a = c ∧ t a = -a}

private lemma owCo_zmod_two_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := h
  rw [ZMod.natCast_eq_zero_iff 2 p] at h'
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h'
  exact hp2 (le_antisymm hle hp.two_le)

private theorem owCo_classRefl_iff_field {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {d : ℕ} (w : Fin d → K) (c : K) (hc : c ≠ 0) (t : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
    t ∈ owCo_classRefl (QuadraticMap.weightedSumSquares K w) c ↔
      ∃ a : Fin d → K, (∑ i, w i * (a i * a i)) = c ∧
        ∀ v : Fin d → K, t v = v - ((2 * c⁻¹) * ∑ i, w i * (v i * a i)) • a := by
  let Q : QuadraticForm K (Fin d → K) := QuadraticMap.weightedSumSquares K w
  have hQapply : ∀ v : Fin d → K, Q v = ∑ i, w i * (v i * v i) := by
    intro v
    simp only [Q, QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  have hQpolar : ∀ x y : Fin d → K,
      QuadraticMap.polar Q x y = 2 * ∑ i, w i * (x i * y i) := by
    intro x y
    exact owCo_polar_weightedSumSquares (K := K) w x y
  have hcinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have hcmul : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  simp only [owCo_classRefl, owCo_isRefl, Set.mem_setOf_eq]
  constructor
  ·
    rintro ⟨⟨ht_inv, ht_rank⟩, ht_isom, a, haQ, hta⟩
    have ha0 : a ≠ 0 := by
      intro h0
      apply hc
      rw [← haQ, h0]
      exact QuadraticMap.map_zero Q
    let φ : (Fin d → K) →ₗ[K] (Fin d → K) :=
      (t : (Fin d → K) →ₗ[K] (Fin d → K)) - LinearMap.id
    have hφa : φ a = (-2 : K) • a := by
      simp only [φ, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hta]
      module
    have hφa0 : φ a ≠ 0 := by
      rw [hφa]
      intro h
      have hneg2 : (-2 : K) ≠ 0 := neg_ne_zero.mpr h2
      have h' : a = 0 := by
        have h3 : ((-2 : K))⁻¹ • ((-2 : K) • a) = 0 := by rw [h, smul_zero]
        rw [smul_smul, inv_mul_cancel₀ hneg2, one_smul] at h3
        exact h3
      exact ha0 h'
    have ht_rank' : Module.finrank K (LinearMap.range φ) = 1 := by
      simpa only [φ] using ht_rank
    have hspan : LinearMap.range φ = Submodule.span K {a} := by
      have hle : Submodule.span K {φ a} ≤ LinearMap.range φ :=
        (Submodule.span_singleton_le_iff_mem (φ a) (LinearMap.range φ)).mpr
          (LinearMap.mem_range.mpr ⟨a, rfl⟩)
      have hfin : Module.finrank K (Submodule.span K {φ a}) = 1 :=
        finrank_span_singleton hφa0
      have heq1 : Submodule.span K {φ a} = LinearMap.range φ :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, ht_rank'])
      have heq2 : Submodule.span K {φ a} = Submodule.span K {a} := by
        apply le_antisymm
        · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
          exact ⟨-2, hφa.symm⟩
        · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
          exact ⟨(-2)⁻¹, by
            rw [hφa, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h2), one_smul]⟩
      rw [← heq1, heq2]
    have hex : ∀ v : Fin d → K, ∃ s : K, φ v = s • a := by
      intro v
      have hv : φ v ∈ Submodule.span K {a} := by
        rw [← hspan]
        exact LinearMap.mem_range.mpr ⟨v, rfl⟩
      rw [Submodule.mem_span_singleton] at hv
      obtain ⟨s, hs⟩ := hv
      exact ⟨s, hs.symm⟩
    let s : (Fin d → K) → K := fun v => Classical.choose (hex v)
    have hs_spec : ∀ v, φ v = s v • a := fun v => Classical.choose_spec (hex v)
    have hs_unique : ∀ {s₁ s₂ : K}, s₁ • a = s₂ • a → s₁ = s₂ := by
      intro s₁ s₂ h
      have h' : (s₁ - s₂) • a = 0 := by rw [sub_smul, h, sub_self]
      by_contra hne
      have hne' : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
      have h'' : a = 0 := by
        have h3 := congrArg (fun x => (s₁ - s₂)⁻¹ • x) h'
        simpa [smul_smul, inv_mul_cancel₀ hne'] using h3
      exact ha0 h''
    have ht_eq : ∀ v, t v = v + s v • a := by
      intro v
      have h := hs_spec v
      simp only [φ, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h
      exact (sub_eq_iff_eq_add.mp h).trans (by rw [add_comm])
    have hs_add : ∀ (v : Fin d → K) (k : K), s (v + k • a) = s v - 2 * k := by
      intro v k
      apply hs_unique
      have hthis : φ (v + k • a) = (s v - 2 * k) • a := by
        rw [map_add, map_smul, hs_spec v, hφa]
        module
      rw [← hs_spec (v + k • a), hthis]
    have hs_val : ∀ v, s v = -(c⁻¹ * QuadraticMap.polar Q v a) := by
      intro v
      obtain ⟨k, hk⟩ : ∃ k : K, 2 * k = s v - 1 :=
        ⟨(s v - 1) * 2⁻¹, by
          rw [show 2 * ((s v - 1) * 2⁻¹) = (s v - 1) * (2 * 2⁻¹) by ring,
              mul_inv_cancel₀ h2, mul_one]⟩
      have hsw : s (v + k • a) = 1 := by rw [hs_add, hk]; ring
      have htw : t (v + k • a) = (v + k • a) + a := by rw [ht_eq, hsw, one_smul]
      have hisow : Q ((v + k • a) + a) = Q (v + k • a) := by
        rw [← htw]
        exact ht_isom (v + k • a)
      have hpol : QuadraticMap.polar Q (v + k • a) a
          = QuadraticMap.polar Q v a + (s v - 1) * c := by
        rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_self, haQ]
        congr 1
        have hkc : k • (2 • c) = (s v - 1) * c := by
          simp only [nsmul_eq_mul, smul_eq_mul]
          linear_combination c * hk
        exact hkc
      have h0 : Q a + QuadraticMap.polar Q (v + k • a) a = 0 := by
        rw [QuadraticMap.map_add Q (v + k • a) a] at hisow
        linear_combination hisow
      have h1 : QuadraticMap.polar Q v a + s v * c = 0 := by
        rw [hpol, haQ] at h0
        linear_combination h0
      have hsv : s v * c = -QuadraticMap.polar Q v a := by linear_combination h1
      calc s v = s v * c * c⁻¹ := by rw [mul_assoc, hcmul, mul_one]
        _ = -QuadraticMap.polar Q v a * c⁻¹ := by rw [hsv]
        _ = -(c⁻¹ * QuadraticMap.polar Q v a) := by ring
    refine ⟨a, ?_, ?_⟩
    · rw [← hQapply a]
      exact haQ
    · intro v
      have hlam : c⁻¹ * QuadraticMap.polar Q v a = (2 * c⁻¹) * ∑ i, w i * (v i * a i) := by
        rw [hQpolar v a]
        ring
      rw [ht_eq v, hs_val v, hlam, neg_smul, sub_eq_add_neg]
  ·
    rintro ⟨a, ha_sum, ht⟩
    have haQ : Q a = c := by rw [hQapply a]; exact ha_sum
    have ha0 : a ≠ 0 := by
      intro h0
      apply hc
      rw [← haQ, h0]
      exact QuadraticMap.map_zero Q
    have hQa2 : QuadraticMap.polar Q a a = 2 * c := by
      rw [hQpolar a a, ha_sum]
    let lam : (Fin d → K) → K := fun v => c⁻¹ * QuadraticMap.polar Q v a
    have hlam_eq : ∀ v, lam v = (2 * c⁻¹) * ∑ i, w i * (v i * a i) := by
      intro v
      simp only [lam, hQpolar v a]
      ring
    have ht' : ∀ v, t v = v - lam v • a := by
      intro v
      rw [ht v, ← hlam_eq v]
    have hlam_a : lam a = 2 := by
      simp only [lam, hQa2]
      rw [show c⁻¹ * (2 * c) = 2 * (c⁻¹ * c) by ring, hcinv, mul_one]
    have hpolar_eq : ∀ v, QuadraticMap.polar Q v a = lam v * c := by
      intro v
      simp only [lam]
      rw [show c⁻¹ * QuadraticMap.polar Q v a * c
            = QuadraticMap.polar Q v a * (c⁻¹ * c) by ring, hcinv, mul_one]
    have hlam_tv : ∀ v, lam (t v) = -lam v := by
      intro v
      have hp : QuadraticMap.polar Q (t v) a = QuadraticMap.polar Q v a - lam v * (2 * c) := by
        rw [ht' v, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, smul_eq_mul, hQa2]
      show c⁻¹ * QuadraticMap.polar Q (t v) a = -(c⁻¹ * QuadraticMap.polar Q v a)
      rw [hp, hpolar_eq v]
      ring
    have ht_inv : t * t = 1 := by
      apply LinearEquiv.ext
      intro v
      rw [LinearEquiv.mul_apply]
      change t (t v) = v
      rw [ht' (t v), hlam_tv v, ht' v]
      module
    have hta : t a = -a := by rw [ht' a, hlam_a]; module
    let f : (Fin d → K) →ₗ[K] (Fin d → K) :=
      (t : (Fin d → K) →ₗ[K] (Fin d → K)) - LinearMap.id
    have hsub_a : f a = (-2 : K) • a := by
      simp only [f, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hta]
      module
    have hrange : LinearMap.range f = Submodule.span K {a} := by
      apply le_antisymm
      · intro y hy
        obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hy
        have hv : f v = -(lam v) • a := by
          simp only [f, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, ht' v]
          module
        rw [hv]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · rw [Submodule.span_singleton_le_iff_mem]
        refine LinearMap.mem_range.mpr ⟨((-2 : K))⁻¹ • a, ?_⟩
        rw [map_smul, hsub_a, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h2), one_smul]
    have ht_rank : Module.finrank K (LinearMap.range f) = 1 := by
      rw [hrange, finrank_span_singleton ha0]
    have ht_isom : ∀ v, Q (t v) = Q v := by
      intro v
      rw [ht' v]
      have hexp : Q (v - lam v • a)
          = Q v + (lam v * lam v) * Q a - lam v * QuadraticMap.polar Q v a := by
        rw [sub_eq_add_neg, ← neg_smul, owCo_quad_expand]
        ring
      rw [hexp, haQ, hpolar_eq v]
      ring
    exact ⟨⟨ht_inv, ht_rank⟩, ht_isom, a, haQ, hta⟩

theorem wit_coord_classRefl_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ} (w : Fin d → ZMod p) (c : ZMod p) (hc : c ≠ 0)
    (t : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) :
    t ∈ ClassRefl p (QuadraticMap.weightedSumSquares (ZMod p) w) c ↔
      ∃ a : Fin d → ZMod p, (∑ i, w i * (a i * a i)) = c ∧
        ∀ v : Fin d → ZMod p, t v = v - ((2 * c⁻¹) * ∑ i, w i * (v i * a i)) • a := by
  exact @owCo_classRefl_iff_field (ZMod p) (@ZMod.instField p ⟨hp⟩)
    (owCo_zmod_two_ne_zero hp hp2) d w c hc t

end CFSG.StandardType.ZS

end
