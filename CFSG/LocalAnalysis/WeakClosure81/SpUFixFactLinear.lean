module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactLinearA
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem spUFix_linear_false {F V : Type*} [Field F] [Finite F] [CharP F 2] [AddCommGroup V]
    [Module F V] {σ : F ≃+* F} (hσ : σ ≠ 1) (ψ : V →+ V)
    (hψ : ∀ (c : F) (v : V), ψ (c • v) = σ c • ψ v) (hψinj : Function.Injective ψ)
    (M : V →ₗ[F] V) {c₀ : F} (hM : ∀ v, M (M v) = c₀ • v)
    (S : Submodule F V) (hψS : ∀ v ∈ S, ψ v ∈ S) (hψ2 : ∀ v ∈ S, ∃ c : F, ψ (ψ v) = c • v)
    {a u : V} (ha : a ∈ S) (hu : u ∈ S) (ha0 : a ≠ 0) (hau : ∀ c : F, u ≠ c • a)
    (hfix : ∀ v ∈ S, v ≠ 0 → ((∃ c : F, ψ v = c • v) ↔ (∃ c : F, M v = c • v))) : False := by
  obtain ⟨d, hd0, hSW⟩ :=
    spUFix_exists_fixed_span hσ ψ hψ hψinj S hψS hψ2 ha hu ha0 hau
  let A : Set V := {x | x ∈ S ∧ d • ψ x = x}
  have hSW' : S ≤ Submodule.span F A := hSW
  have hcombo : ∀ p q : F, p • a + q • u = 0 → p = 0 ∧ q = 0 := by
    intro p q hpq
    have hq : q = 0 := by
      by_contra hq0
      have hqsmul : q • u = -(p • a) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hpq
      have hu_eq : u = (q⁻¹ * (-p)) • a := by
        have hcancel : q⁻¹ • (q • u) = q⁻¹ • (-(p • a)) :=
          congrArg (fun w => q⁻¹ • w) hqsmul
        rw [smul_smul, inv_mul_cancel₀ hq0, one_smul] at hcancel
        rw [hcancel, smul_neg, ← neg_smul, smul_smul, neg_mul, mul_neg]
      exact hau (q⁻¹ * (-p)) hu_eq
    rw [hq, zero_smul, add_zero] at hpq
    have hp : p = 0 := by
      by_contra hp0
      have hc : p⁻¹ • (p • a) = p⁻¹ • (0 : V) := congrArg (fun w => p⁻¹ • w) hpq
      rw [smul_smul, inv_mul_cancel₀ hp0, one_smul, smul_zero] at hc
      exact ha0 hc
    exact ⟨hp, hq⟩
  have hA_eig : ∀ x ∈ A, x ≠ 0 → ∃ μ : F, M x = μ • x ∧ μ * μ = c₀ := by
    intro x hxA hx0
    have hxS : x ∈ S := hxA.1
    have hdx : d • ψ x = x := hxA.2
    have hψx : ψ x = d⁻¹ • x := by
      have := congrArg (fun y => d⁻¹ • y) hdx
      simpa [smul_smul, inv_mul_cancel₀ hd0] using this
    obtain ⟨μ, hμ⟩ := (hfix x hxS hx0).1 ⟨d⁻¹, hψx⟩
    refine ⟨μ, hμ, ?_⟩
    have hMM : M (M x) = (μ * μ) • x := by
      rw [hμ, map_smul, hμ, smul_smul]
    have hc : (μ * μ) • x = c₀ • x := by rw [← hMM, hM x]
    by_contra hne
    have hne' : μ * μ - c₀ ≠ 0 := sub_ne_zero.mpr hne
    have hzero : (μ * μ - c₀) • x = 0 := by rw [sub_smul, hc, sub_self]
    have hx0' : x = 0 := by
      have hcongr := congrArg (fun w => (μ * μ - c₀)⁻¹ • w) hzero
      rw [smul_smul, inv_mul_cancel₀ hne', one_smul, smul_zero] at hcongr
      exact hcongr
    exact hx0 hx0'
  have hA_exists : ∃ x₀ ∈ A, x₀ ≠ 0 := by
    by_contra h
    have hzero : ∀ x ∈ A, x = 0 := by
      intro x hx
      by_contra hx0
      exact h ⟨x, hx, hx0⟩
    have hspan : Submodule.span F A = ⊥ := Submodule.span_eq_bot.mpr hzero
    have : a ∈ (⊥ : Submodule F V) := by
      rw [← hspan]
      exact hSW' ha
    exact ha0 (by simpa using this)
  obtain ⟨x₀, hx₀A, hx₀0⟩ := hA_exists
  obtain ⟨μ₀, hμ₀x, hμ₀sq⟩ := hA_eig x₀ hx₀A hx₀0
  have hMA : ∀ x ∈ A, M x = μ₀ • x := by
    intro x hxA
    by_cases hx0 : x = 0
    · rw [hx0, map_zero, smul_zero]
    · obtain ⟨μ, hμ, hμsq⟩ := hA_eig x hxA hx0
      have hμμ₀ : μ = μ₀ := by
        have hsq : μ ^ 2 = μ₀ ^ 2 := by rw [pow_two, pow_two, hμsq, hμ₀sq]
        exact (CharTwo.sq_inj (R := F)).1 hsq
      rw [hμ, hμμ₀]
  have hSlin : ∀ v ∈ S, M v = μ₀ • v := by
    intro v hv
    exact Submodule.span_induction (p := fun x _ => M x = μ₀ • x)
      (fun x hx => hMA x hx) (by simp)
      (fun x y _ _ hx hy => by rw [map_add, hx, hy, smul_add])
      (fun c x _ hx => by rw [map_smul, hx, smul_comm])
      (hSW' hv)
  have heig : ∀ v ∈ S, v ≠ 0 → ∃ c : F, ψ v = c • v := by
    intro v hv hv0
    exact (hfix v hv hv0).2 ⟨μ₀, hSlin v hv⟩
  obtain ⟨c₁, hc₁⟩ := heig a ha ha0
  have hu0 : u ≠ 0 := by simpa using hau 0
  obtain ⟨c₂, hc₂⟩ := heig u hu hu0
  have hψa0 : ψ a ≠ 0 := by
    intro h0
    exact ha0 (hψinj (by rw [h0, map_zero]))
  have hc1 : c₁ ≠ 0 := by
    intro h
    exact hψa0 (by rw [hc₁, h, zero_smul])
  have hcoeff : ∀ t : F, ∃ ct : F, c₁ = ct ∧ σ t * c₂ = ct * t := by
    intro t
    have htuS : a + t • u ∈ S := S.add_mem ha (S.smul_mem t hu)
    have htu0 : a + t • u ≠ 0 := by
      intro h0
      have h0' : (1 : F) • a + t • u = 0 := by simpa using h0
      obtain ⟨h1, -⟩ := hcombo 1 t h0'
      exact one_ne_zero h1
    obtain ⟨ct, hct⟩ := heig (a + t • u) htuS htu0
    have hL : ψ (a + t • u) = c₁ • a + (σ t * c₂) • u := by
      rw [map_add, hψ t u, hc₁, hc₂, smul_smul]
    have hR : ct • (a + t • u) = ct • a + (ct * t) • u := by
      rw [smul_add, smul_smul]
    have hcomp : c₁ • a + (σ t * c₂) • u = ct • a + (ct * t) • u := by
      rw [← hL, hct, hR]
    have hdiff : (c₁ - ct) • a + (σ t * c₂ - ct * t) • u
        = (c₁ • a + (σ t * c₂) • u) - (ct • a + (ct * t) • u) := by
      rw [sub_smul, sub_smul, sub_add_sub_comm]
    have hzero : (c₁ - ct) • a + (σ t * c₂ - ct * t) • u = 0 := by
      rw [hdiff, hcomp, sub_self]
    obtain ⟨h1, h2⟩ := hcombo (c₁ - ct) (σ t * c₂ - ct * t) hzero
    exact ⟨ct, sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  have hc2c1 : c₂ = c₁ := by
    obtain ⟨c1', hc1', h1'⟩ := hcoeff 1
    rw [map_one, one_mul, mul_one] at h1'
    exact h1'.trans hc1'.symm
  have hσt : ∀ t : F, σ t = t := by
    intro t
    obtain ⟨ct, hc1t, hst⟩ := hcoeff t
    rw [hc2c1, ← hc1t] at hst
    exact mul_right_cancel₀ hc1 (hst.trans (mul_comm c₁ t))
  have hσ1 : σ = 1 := by
    ext t
    simpa using hσt t
  exact hσ hσ1

end CFSG.LocalAnalysis.WeakClosure81

end
