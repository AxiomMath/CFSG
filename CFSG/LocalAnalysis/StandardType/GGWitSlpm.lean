module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

open Subgroup

private theorem wSlpm_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := h
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h'
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

private theorem wSlpm_one_sub_two (p : ℕ) : (1 : ZMod p) - 2 = -1 := by ring

private theorem wSlpm_one_add_one (p : ℕ) : (1 : ZMod p) + 1 = 2 := by ring

private theorem wSlpm_inv_two_mul_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p)⁻¹ * 2 = 1 :=
  inv_mul_cancel₀ (wSlpm_two_ne_zero hp2)

private theorem wSlpm_x_mul_inv_two_mul_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (x : ZMod p) : x * (2 : ZMod p)⁻¹ * 2 = x := by
  rw [mul_assoc, wSlpm_inv_two_mul_two hp2, mul_one]

private theorem wSlpm_two_mul_inv_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) * 2⁻¹ = 1 := by
  rw [mul_comm, wSlpm_inv_two_mul_two hp2]

private theorem wSlpm_mul_inv_two_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {t : ZMod p} (h : t * (2 : ZMod p)⁻¹ = 0) : t = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd h (inv_ne_zero (wSlpm_two_ne_zero hp2))

private theorem wSlpm_mul_two_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {s : ZMod p}
    (h : s * 2 = 0) : s = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd h (wSlpm_two_ne_zero hp2)

private theorem wSlpm_smul_eq_zero_left {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {t : K} {b : V} (hb : b ≠ 0) (h : t • b = 0) : t = 0 := by
  rcases smul_eq_zero.mp h with h | h
  · exact h
  · exact absurd h hb

theorem slpmRefl_involutive {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) :
    Function.Involutive (fun v : U => v - α v • a) := by
  intro v
  have h := Module.involutive_preReflection (x := a) (f := α) hα
  simpa only [Module.preReflection_apply] using h v

@[expose] def slpmRefl {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) : U ≃ₗ[ZMod p] U :=
  LinearEquiv.ofInvolutive (LinearMap.id - α.smulRight a) (slpmRefl_involutive a α hα)

private theorem wSlpm_slpmRefl_apply {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) (v : U) :
    (slpmRefl a α hα) v = v - α v • a := rfl

private theorem wSlpm_slpmRefl_toLinearMap {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) :
    (slpmRefl a α hα : U →ₗ[ZMod p] U) = LinearMap.id - α.smulRight a := rfl

private theorem wSlpm_slpmRefl_eq_reflection {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) :
    slpmRefl a α hα = Module.reflection (x := a) (f := α) hα := by
  apply LinearEquiv.ext
  intro v
  rw [wSlpm_slpmRefl_apply a α hα v, Module.reflection_apply]

private theorem wSlpm_det_preReflection {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) :
    LinearMap.det (Module.preReflection a α) = -1 := by
  classical
  let b := Module.finBasis (ZMod p) U
  let A : Matrix (Fin 1) (Fin (Module.finrank (ZMod p) U)) (ZMod p) := fun _ j => α (b j)
  let B : Matrix (Fin (Module.finrank (ZMod p) U)) (Fin 1) (ZMod p) := fun i _ => b.repr a i
  have hmat : (LinearMap.toMatrix b b) (α.smulRight a) = B * A := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.smulRight_apply, Matrix.mul_apply]
    simp only [A, B, Fin.sum_univ_one]
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    ring
  have hsum : (∑ i, α (b i) * b.repr a i) = α a := by
    conv_rhs => rw [← b.sum_repr a]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul, smul_eq_mul, mul_comm]
  have hAB : (A * B) 0 0 = α a := by
    rw [Matrix.mul_apply]
    change (∑ i, α (b i) * b.repr a i) = α a
    exact hsum
  have h1 : LinearMap.det (LinearMap.id - α.smulRight a) = (1 - B * A).det := by
    rw [← LinearMap.det_toMatrix b (LinearMap.id - α.smulRight a)]
    rw [map_sub, LinearMap.toMatrix_id, hmat]
    rfl
  have h2 : (1 - B * A).det = (1 - A * B).det := Matrix.det_one_sub_mul_comm B A
  have h3 : (1 - A * B).det = 1 - α a := by
    rw [Matrix.det_fin_one, Matrix.sub_apply, Matrix.one_apply, hAB]
    simp
  rw [Module.preReflection, h1, h2, h3, hα]
  exact wSlpm_one_sub_two p

theorem slpm_refl_form {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] {r : U ≃ₗ[ZMod p] U} (hr : IsRefl p r) :
    ∃ (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2), r = slpmRefl a α hα := by
  obtain ⟨hr2, hrk⟩ := hr
  let W : Submodule (ZMod p) U :=
    LinearMap.range ((r : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U))
  have hWk : Module.finrank (ZMod p) W = 1 := hrk
  have hWne : W ≠ ⊥ := by
    intro hbot
    have : Module.finrank (ZMod p) W = 0 := (Submodule.finrank_eq_zero).mpr hbot
    omega
  obtain ⟨a, haW, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hspan : Submodule.span (ZMod p) {a} = W := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · exact (Submodule.span_singleton_le_iff_mem a W).mpr haW
    · rw [finrank_span_singleton ha0, hWk]
  have hra : (r : U →ₗ[ZMod p] U) a = -a := by
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp haW
    have hrv : (r : U →ₗ[ZMod p] U) ((r : U →ₗ[ZMod p] U) v) = v := by
      have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hr2
      simpa [LinearEquiv.mul_apply] using h
    rw [← hv]
    simp only [LinearMap.sub_apply, LinearMap.id_apply]
    rw [map_sub, hrv]
    abel
  obtain ⟨lam, hlam⟩ : ∃ lam : U →ₗ[ZMod p] ZMod p, lam a = 1 := by
    have hli : LinearIndependent (ZMod p) (fun _ : Unit => a) :=
      linearIndependent_unique_iff.mpr ha0
    obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one hli.linearIndepOn_id
    exact ⟨f, hf a ⟨(), rfl⟩⟩
  let α : U →ₗ[ZMod p] ZMod p :=
    lam.comp ((LinearMap.id : U →ₗ[ZMod p] U) - (r : U →ₗ[ZMod p] U))
  have hα : α a = 2 := by
    simp only [α, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [hra]
    simp only [sub_neg_eq_add, map_add, hlam]
    exact wSlpm_one_add_one p
  have hrv : ∀ v : U, r v = v - α v • a := by
    intro v
    have hmem : ((r : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) v
        ∈ Submodule.span (ZMod p) {a} := by
      rw [hspan]
      exact ⟨v, rfl⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    have hαv : α v = -t := by
      simp only [α, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
      have hstep : v - (r : U →ₗ[ZMod p] U) v = -(t • a) := by
        rw [show v - (r : U →ₗ[ZMod p] U) v = -((r : U →ₗ[ZMod p] U) v - v) by abel]
        have h' : (r : U →ₗ[ZMod p] U) v - v = t • a := by
          simpa only [LinearMap.sub_apply, LinearMap.id_apply] using ht.symm
        rw [h']
      rw [hstep, map_neg, map_smul, hlam, smul_eq_mul, mul_one]
    have hkey : α v • a = -(t • a) := by rw [hαv]; exact neg_smul t a
    rw [hkey, ht]
    simp only [LinearMap.sub_apply, LinearMap.id_apply]
    abel
  refine ⟨a, α, hα, ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [hrv v, wSlpm_slpmRefl_apply a α hα v]

theorem slpmRefl_isRefl_det {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p)
    (hα : α a = 2) :
    IsRefl p (slpmRefl a α hα) ∧ LinearEquiv.det (slpmRefl a α hα) = -1 := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpm_two_ne_zero hp2
  have ha0 : a ≠ 0 := by
    intro h; rw [h, map_zero] at hα; exact h2 hα.symm
  have hα0 : α ≠ 0 := by
    intro h; rw [h, LinearMap.zero_apply] at hα; exact h2 hα.symm
  constructor
  · constructor
    · rw [wSlpm_slpmRefl_eq_reflection a α hα]
      ext v
      simpa [LinearEquiv.mul_apply] using
        Module.involutive_reflection (x := a) (f := α) hα v
    · rw [wSlpm_slpmRefl_toLinearMap a α hα]
      have hrange : LinearMap.range ((LinearMap.id - α.smulRight a : U →ₗ[ZMod p] U) - LinearMap.id)
          = LinearMap.range (α.smulRight a) := by
        apply le_antisymm
        · rintro x ⟨v, rfl⟩
          exact ⟨-v, by
            simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
              map_neg, neg_smul, neg_neg]
            abel⟩
        · rintro x ⟨v, rfl⟩
          exact ⟨-v, by
            simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
              map_neg, neg_smul, neg_neg]
            abel⟩
      rw [hrange, LinearMap.range_smulRight_apply hα0 a]
      exact finrank_span_singleton ha0
  · rw [wSlpm_slpmRefl_eq_reflection a α hα, ← Units.val_eq_neg_one, LinearEquiv.coe_det]
    exact wSlpm_det_preReflection a α hα

theorem slpm_exists_partner {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (hd : 3 ≤ Module.finrank (ZMod p) U)
    (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) :
    ∃ (b : U) (β : U →ₗ[ZMod p] ZMod p) (hβ : β b = 2), α b = 0 ∧ β a = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpm_two_ne_zero hp2
  have ha0 : a ≠ 0 := by
    intro h; rw [h, map_zero] at hα; exact h2 hα.symm
  have hspan_ne : Submodule.span (ZMod p) {a} ≠ ⊤ := by
    intro htop
    have hfr : Module.finrank (ZMod p) (Submodule.span (ZMod p) {a}) = Module.finrank (ZMod p) U := by
      rw [htop, finrank_top]
    rw [finrank_span_singleton ha0] at hfr
    omega
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : U, b₀ ∉ Submodule.span (ZMod p) {a} := by
    by_contra h
    have h' : ∀ x : U, x ∈ Submodule.span (ZMod p) {a} := by
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    exact hspan_ne (Submodule.eq_top_iff'.mpr h')
  let b : U := b₀ - (α b₀ * (2 : ZMod p)⁻¹) • a
  have hαb : α b = 0 := by
    change α (b₀ - (α b₀ * (2 : ZMod p)⁻¹) • a) = 0
    rw [map_sub, map_smul, hα, smul_eq_mul]
    rw [wSlpm_x_mul_inv_two_mul_two hp2 (α b₀)]
    exact sub_self _
  have hb0 : b ≠ 0 := by
    intro hb
    apply hb₀
    have hb_eq : b₀ = (α b₀ * (2 : ZMod p)⁻¹) • a := by
      have h := hb
      simp only [b] at h
      exact sub_eq_zero.mp h
    rw [hb_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton a))
  have hv : LinearIndependent (ZMod p) ![a, (2 : ZMod p)⁻¹ • b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hst' : s • a + (t * (2 : ZMod p)⁻¹) • b = 0 := by
      simpa only [smul_smul] using hst
    have hαst : α (s • a + (t * (2 : ZMod p)⁻¹) • b) = 0 := by rw [hst', map_zero]
    have hs : s = 0 := by
      simp only [map_add, map_smul, hα, hαb, smul_eq_mul, smul_zero, mul_zero,
        add_zero] at hαst
      exact wSlpm_mul_two_eq_zero hp2 hαst
    refine ⟨hs, ?_⟩
    have ht : (t * (2 : ZMod p)⁻¹) • b = 0 := by
      rw [hs, zero_smul, zero_add] at hst'
      exact hst'
    exact wSlpm_mul_inv_two_eq_zero hp2 (wSlpm_smul_eq_zero_left hb0 ht)
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one hv.linearIndepOn_id
  have hfa : f a = 1 := hf a ⟨0, rfl⟩
  have hfb : f ((2 : ZMod p)⁻¹ • b) = 1 := hf ((2 : ZMod p)⁻¹ • b) ⟨1, rfl⟩
  let β : U →ₗ[ZMod p] ZMod p := f
  have hβa : β a = 1 := hfa
  have hβb : β b = 2 := by
    have hb_eq : b = (2 : ZMod p) • ((2 : ZMod p)⁻¹ • b) := by
      rw [smul_smul, wSlpm_two_mul_inv_two hp2, one_smul]
    rw [hb_eq, map_smul, hfb, smul_eq_mul, mul_one]
  exact ⟨b, β, hβb, hαb, hβa⟩

end CFSG.StandardType.ZS

end
