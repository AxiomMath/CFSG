module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

public section

namespace CFSG.RankThree.PartOne.KCUnitaryHerm

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_bar_mul_eq {d : K} (hd : h.bar d = d) : ∃ u : K, h.bar u * u = d := by
  obtain ⟨u, hu⟩ := h.normHom_surjective ⟨d, hd⟩
  refine ⟨u, ?_⟩
  have := congrArg Subtype.val hu
  rw [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at this
  rw [mul_comm, this]

theorem exists_add_bar_eq {d : K} (hd : h.bar d = d) : ∃ a : K, a + h.bar a = d := by
  obtain ⟨a, ha⟩ := h.traceLin_surjective ⟨d, hd⟩
  refine ⟨a, ?_⟩
  have := congrArg Subtype.val ha
  simpa [UnitaryFieldData.trace] using this

theorem two_ne_zero_of_gt_three (h : UnitaryFieldData p f K) (hp3 : 3 < p) : (2 : K) ≠ 0 := by
  intro h2
  have := h.charP
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h2)
  have := Nat.le_of_dvd (by norm_num) hd
  omega

theorem exists_traceZero (h : UnitaryFieldData p f K) : ∃ η : K, h.bar η = -η ∧ η ≠ 0 := by
  obtain ⟨η, hη, hη0⟩ := h.exists_mem_traceZero_ne_zero
  exact ⟨η, eq_neg_of_add_eq_zero_right (h.mem_traceZero.mp hη), hη0⟩

variable {V : Type} [AddCommGroup V] [Module K V]

theorem eq_zero_of_forall_diag_eq_zero (hp3 : 3 < p) (ψ : V → V → K)
    (hadd₁ : ∀ x y z, ψ (x + y) z = ψ x z + ψ y z)
    (hadd₂ : ∀ x y z, ψ x (y + z) = ψ x y + ψ x z)
    (hsmul₁ : ∀ (c : K) x y, ψ (c • x) y = h.bar c * ψ x y)
    (hsmul₂ : ∀ (c : K) x y, ψ x (c • y) = c * ψ x y)
    (hherm : ∀ x y, ψ y x = h.bar (ψ x y)) (h0 : ∀ x, ψ x x = 0) (x y : V) : ψ x y = 0 := by
  obtain ⟨η, hη, hη0⟩ := exists_traceZero h
  have h1 := h0 (x + y)
  simp only [hadd₁, hadd₂, h0, hherm x y, zero_add, add_zero] at h1
  have h2 := h0 (x + η • y)
  simp only [hadd₁, hadd₂, hsmul₁, hsmul₂, h0, hherm x y, hη, zero_add, add_zero,
    mul_zero] at h2
  have h3 : (2 * η) * ψ x y = 0 := by
    have h4 : h.bar (ψ x y) = -ψ x y := by linear_combination h1
    rw [h4] at h2
    linear_combination h2
  exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero (two_ne_zero_of_gt_three h hp3) hη0)

variable {h}

theorem exists_hyperbolic_pair_of_sq_zero (hp3 : 3 < p) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {N : V →ₗ[K] V}
    (hN : ∀ x y, B (N x) y = -B x (N y)) (hN2 : ∀ x, N (N x) = 0) (hN0 : N ≠ 0)
    {η₀ : K} (hη₀ : h.bar η₀ = -η₀) (hη₀0 : η₀ ≠ 0) :
    ∃ e g : V, B e e = 0 ∧ B g g = 0 ∧ B e g = 1 ∧ N e = 0 ∧ N g = η₀ • e := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  have hbar_inv : ∀ c : K, h.bar c⁻¹ = (h.bar c)⁻¹ := fun c => map_inv₀ h.bar c
  obtain ⟨w, hw⟩ : ∃ w, B w (N w) ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ w, B w (N w) = 0 := fun w => by
      by_contra hne
      exact hcon ⟨w, hne⟩
    apply hN0
    refine LinearMap.ext fun y => ?_
    have hψ := eq_zero_of_forall_diag_eq_zero h hp3 (V := V)
      (fun x y => η₀⁻¹ * B x (N y))
      (fun x y z => by simp only [map_add, LinearMap.add_apply, mul_add])
      (fun x y z => by simp only [map_add, mul_add])
      (fun c x y => by
        simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
        ring)
      (fun c x y => by
        simp only [map_smul, smul_eq_mul]
        ring)
      (fun x y => by
        rw [map_mul, hbar_inv, hη₀, ← hsymm x (N y), hN y x]
        ring)
      (fun x => by rw [hcon' x, mul_zero])
    have hz : ∀ x, B x (N y) = 0 := fun x => by
      have := hψ x y
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (inv_eq_zero.mp h1) hη₀0
      · exact h1
    have hz' : N y = 0 := hBl (N y) fun x => by
      rw [hsymm x (N y), hz x, map_zero]
    simpa using hz'
  set t := B w (N w) with ht
  have hbt : h.bar t = -t := by
    rw [ht, ← hsymm w (N w), hN w w]
  have hs0 : h.bar (η₀ * t) = η₀ * t := by
    rw [map_mul, hη₀, hbt]
    ring
  obtain ⟨μ, hμ⟩ := exists_bar_mul_eq h (d := -(η₀ * t)⁻¹) (by rw [map_neg, hbar_inv, hs0])
  set w₁ := μ • w with hw₁
  have hw₁N : B w₁ (N w₁) = -η₀⁻¹ := by
    have h1 : B w₁ (N w₁) = (h.bar μ * μ) * t := by
      simp only [hw₁, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      rw [ht]
      ring
    rw [h1, hμ]
    field_simp
  set e := N w₁ with he
  have hee : B e e = 0 := by rw [he, hN w₁ (N w₁), hN2 w₁, map_zero, neg_zero]
  have hNe : N e = 0 := hN2 w₁
  have hew : B e w₁ = η₀⁻¹ := by rw [he, hN w₁ w₁, hw₁N, neg_neg]
  set g₀ := η₀ • w₁ with hg₀
  have heg₀ : B e g₀ = 1 := by
    rw [hg₀, map_smul, smul_eq_mul, hew, mul_inv_cancel₀ hη₀0]
  have hNg₀ : N g₀ = η₀ • e := by rw [hg₀, map_smul]
  have hg₀e : B g₀ e = 1 := by rw [hsymm e g₀, heg₀, map_one]
  set s := B g₀ g₀ with hs
  have hsbar : h.bar s = s := (hsymm g₀ g₀).symm
  obtain ⟨a, ha⟩ := exists_add_bar_eq h (d := -s) (by rw [map_neg, hsbar])
  refine ⟨e, g₀ + a • e, hee, ?_, ?_, hNe, ?_⟩
  · simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hee,
      heg₀, hg₀e]
    linear_combination ha
  · simp only [map_add, map_smul, smul_eq_mul, hee, heg₀]
    ring
  · rw [map_add, hNg₀, map_smul, hNe, smul_zero, add_zero]

theorem orthogonal_span_invariant {B : V →ₛₗ[h.bar] V →ₗ[K] K} {N : V →ₗ[K] V}
    (hN : ∀ x y, B (N x) y = -B x (N y)) {e g : V} {η : K} (he : N e = 0) (hg : N g = η • e)
    {z : V} (hz : z ∈ (Submodule.span K {e, g}).orthogonalBilin B) :
    N z ∈ (Submodule.span K {e, g}).orthogonalBilin B := by
  rw [Submodule.mem_orthogonalBilin] at hz ⊢
  intro x hx
  have hNx : N x ∈ Submodule.span K {e, g} := by
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [map_add, map_smul, map_smul, he, hg, smul_zero, zero_add, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact neg_eq_zero.mp ((hN x z).symm.trans (hz (N x) hNx))

end CFSG.RankThree.PartOne.KCUnitaryHerm
