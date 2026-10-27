module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.ZS

open Module CFSG.StandardType.QTwoLin

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem not_transvection {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : TransvectionFree A) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ A)
    {u : U} {χ : Dual (ZMod p) U} (hu : u ≠ 0) (hχu : χ u = 0)
    (h : ∀ v, g v = v + χ v • u) : χ = 0 := by
  by_contra hχ
  exact hA g hg ⟨u, χ, hu, hχ, hχu, h⟩

theorem reflection_eq_of_mem_span (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : TransvectionFree A) {a b : U} {φ ψ : Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (hr : reflection hφ ∈ A) (hs : reflection hψ ∈ A)
    (hab : b ∈ Submodule.span (ZMod p) {a}) : reflection hφ = reflection hψ := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hab
  have ha_ne : a ≠ 0 := by
    rintro rfl
    exact h2 (by simpa using hφ.symm)
  have hψa : ψ (t • a) = 2 := by rwa [ht]
  have htψ : t * ψ a = 2 := by simpa [map_smul, smul_eq_mul] using hψa
  have hformula : ∀ v, (reflection hφ * reflection hψ) v = v + (t • ψ - φ) v • a := by
    intro v
    rw [LinearEquiv.mul_apply, reflection_apply, reflection_apply, ← ht]
    simp only [map_sub, map_smul, hφ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    module
  have hχa : (t • ψ - φ) a = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hφ, htψ]
    ring
  have hχ : t • ψ - φ = 0 := not_transvection hA (mul_mem hr hs) ha_ne hχa hformula
  have hts : t • ψ = φ := sub_eq_zero.mp hχ
  ext v
  rw [reflection_apply, reflection_apply, ← ht]
  have htv : t * ψ v = φ v := by
    have := congrArg (fun f : Dual (ZMod p) U => f v) hts
    simpa [LinearMap.smul_apply, smul_eq_mul] using this
  rw [← htv, smul_smul, mul_comm (ψ v) t]

private theorem exists_smul_eq_of_ker_eq (hp : p ≠ 2) {a b : U} {φ ψ : Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2) (hker : LinearMap.ker φ = LinearMap.ker ψ) :
    ∃ μ : ZMod p, ψ = μ • φ ∧ μ * φ b = 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  set μ : ZMod p := ψ a / (2 : ZMod p) with hμ_def
  have hψ_eq : ψ = μ • φ := by
    ext v
    have hw : v - (φ v / (2 : ZMod p)) • a ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hφ, smul_eq_mul, div_mul_cancel₀ (φ v) h2,
        sub_self]
    have hwψ : ψ (v - (φ v / (2 : ZMod p)) • a) = 0 := by
      have : v - (φ v / (2 : ZMod p)) • a ∈ LinearMap.ker ψ := by rw [← hker]; exact hw
      simpa using this
    calc ψ v = ψ ((v - (φ v / (2 : ZMod p)) • a) + (φ v / (2 : ZMod p)) • a) := by
          rw [sub_add_cancel]
      _ = ψ (v - (φ v / (2 : ZMod p)) • a) + ψ ((φ v / (2 : ZMod p)) • a) := by rw [map_add]
      _ = 0 + (φ v / (2 : ZMod p)) * ψ a := by rw [hwψ, map_smul, smul_eq_mul]
      _ = (μ • φ) v := by
          rw [hμ_def, div_eq_mul_inv, div_eq_mul_inv]
          simp only [LinearMap.smul_apply, smul_eq_mul]
          ring
  refine ⟨μ, hψ_eq, ?_⟩
  have := congrArg (fun f : Dual (ZMod p) U => f b) hψ_eq
  simpa [LinearMap.smul_apply, smul_eq_mul, hψ] using this.symm

theorem reflection_eq_of_ker_eq (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : TransvectionFree A) {a b : U} {φ ψ : Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (hr : reflection hφ ∈ A) (hs : reflection hψ ∈ A)
    (hker : LinearMap.ker φ = LinearMap.ker ψ) : reflection hφ = reflection hψ := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨μ, hψ_eq, hμb⟩ := exists_smul_eq_of_ker_eq hp hφ hψ hker
  have hmul : ∀ x : ZMod p, (μ * x) * φ b = 2 * x := fun x => by
    rw [mul_assoc, mul_comm x (φ b), ← mul_assoc, hμb]
  set c : U := a + μ • b - (μ * φ b) • a with hc_def
  have hφc : φ c = 0 := by
    rw [hc_def]
    simp only [map_sub, map_add, map_smul, hφ, hμb, smul_eq_mul]
    ring
  have hformula : ∀ v, (reflection hφ * reflection hψ) v = v + (-φ) v • c := by
    intro v
    rw [hc_def, LinearEquiv.mul_apply, reflection_apply, reflection_apply, hψ_eq]
    simp only [map_sub, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul, hmul,
      hμb]
    module
  have hφ_ne : φ ≠ 0 := by
    intro h0
    exact h2 (by simpa [h0] using hφ.symm)
  have hc0 : c = 0 := by
    by_contra hc
    have hneg : -φ = 0 :=
      not_transvection hA (mul_mem hr hs) hc (by simp [hφc]) hformula
    exact hφ_ne (neg_eq_zero.mp hneg)
  have hμb_eq : μ • b = a := by
    have h := hc0
    rw [hc_def, hμb] at h
    have h' : μ • b - a = 0 := by
      rw [← h]
      module
    exact sub_eq_zero.mp h'
  ext v
  rw [reflection_apply, reflection_apply, hψ_eq]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [mul_comm μ (φ v), ← smul_smul, hμb_eq]

private theorem apply_eq_zero_of_zero (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : TransvectionFree A) {a b : U} {φ ψ : Dual (ZMod p) U} (hφ : φ a = 2)
    (hψ : ψ b = 2) (hr : reflection hφ ∈ A) (hs : reflection hψ ∈ A)
    (h : φ b = 0) : ψ a = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  set κ : ZMod p := ψ a with hκ_def
  by_contra hκ
  have hb_ne : b ≠ 0 := by
    rintro rfl
    exact h2 (by simpa using hψ.symm)
  have hφ_ne : φ ≠ 0 := by
    intro h0
    exact h2 (by simpa [h0] using hφ.symm)
  have hformula : ∀ v, ((reflection hφ * reflection hψ) ^ 2) v = v + (κ • φ) v • b := by
    intro v
    rw [pow_two, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      reflection_apply, reflection_apply, reflection_apply, reflection_apply]
    simp only [map_sub, map_smul, hφ, hψ, h, LinearMap.smul_apply, smul_eq_mul]
    module
  have hχb : (κ • φ) b = 0 := by
    simp only [LinearMap.smul_apply, smul_eq_mul, h, mul_zero]
  have hzero : κ • φ = 0 :=
    not_transvection hA (pow_mem (mul_mem hr hs) 2) hb_ne hχb hformula
  exact hκ ((smul_eq_zero.mp hzero).resolve_right hφ_ne)

theorem apply_eq_zero_comm (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : TransvectionFree A) {a b : U} {φ ψ : Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (hr : reflection hφ ∈ A) (hs : reflection hψ ∈ A) : φ b = 0 ↔ ψ a = 0 :=
  ⟨apply_eq_zero_of_zero hp hA hφ hψ hr hs,
    fun h => apply_eq_zero_of_zero hp hA (a := b) (b := a) (φ := ψ) (ψ := φ) hψ hφ hs hr h⟩

theorem commute_reflection_iff (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : TransvectionFree A) {a b : U} {φ ψ : Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (hr : reflection hφ ∈ A) (hs : reflection hψ ∈ A)
    (hne : reflection hφ ≠ reflection hψ) :
    Commute (reflection hφ) (reflection hψ) ↔ φ b = 0 := by
  constructor
  · intro hc
    have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have hca := congrArg (fun g : U ≃ₗ[ZMod p] U => g a) hc.eq
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflection_apply, reflection_apply,
      reflection_apply, reflection_apply] at hca
    simp only [map_sub, map_smul, hφ, smul_eq_mul] at hca
    have hmain : (ψ a * φ b) • a = (2 * ψ a) • b := by
      linear_combination (norm := module) hca
    have hψa : ψ a = 0 := by
      by_contra hψa_ne
      have hbspan : b ∈ Submodule.span (ZMod p) {a} := by
        rw [Submodule.mem_span_singleton]
        refine ⟨(2 * ψ a)⁻¹ * (ψ a * φ b), ?_⟩
        have h2ψ : 2 * ψ a ≠ 0 := mul_ne_zero h2 hψa_ne
        calc ((2 * ψ a)⁻¹ * (ψ a * φ b)) • a
            = (2 * ψ a)⁻¹ • ((ψ a * φ b) • a) := by rw [← smul_smul]
          _ = (2 * ψ a)⁻¹ • ((2 * ψ a) • b) := by rw [hmain]
          _ = b := by rw [smul_smul, inv_mul_cancel₀ h2ψ, one_smul]
      exact hne (reflection_eq_of_mem_span hp hA hφ hψ hr hs hbspan)
    exact (apply_eq_zero_comm hp hA hφ hψ hr hs).mpr hψa
  · intro hφb
    have hψa : ψ a = 0 := (apply_eq_zero_comm hp hA hφ hψ hr hs).mp hφb
    show reflection hφ * reflection hψ = reflection hψ * reflection hφ
    ext v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflection_apply, reflection_apply,
      reflection_apply, reflection_apply]
    simp only [map_sub, map_smul, hφb, hψa, smul_eq_mul]
    module

end CFSG.StandardType.ZS
