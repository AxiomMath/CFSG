module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiag
public import CFSG.Milestones.ASVolI.F429.Base

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.BA

section Generic

theorem burnsideF429a_subgroupOf_inf {G : Type} [Group G] (A B K : Subgroup G) :
    (A ⊓ B).subgroupOf K = A.subgroupOf K ⊓ B.subgroupOf K := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem burnsideF429a_inner_of_borelAutData {Y : Type} [Group Y] {U H : Subgroup Y}
    {F : Subgroup (MulAut Y)} (D : BorelAutData U H F) (β : MulAut Y)
    (h1 : ∀ x, β x ∈ U ↔ x ∈ U) (h2 : ∀ h ∈ H, β h * h⁻¹ ∈ U) :
    β ∈ (MulAut.conj : Y →* MulAut Y).range := by
  obtain ⟨g, hg, τ, hτ, rfl⟩ := D.normal_form β h1
  obtain ⟨u₀, hu₀, h₀, hh₀, rfl⟩ := D.B_eq g hg
  have hfix : ∀ h ∈ H, τ h = h := by
    intro h hh
    have hτh : τ h ∈ H := D.F_H τ hτ h hh
    have hc := h2 h hh
    rw [MulAut.mul_apply, MulAut.conj_apply] at hc
    have hcomm : h₀ * τ h = τ h * h₀ := D.H_comm h₀ hh₀ (τ h) hτh
    have e1 : u₀ * h₀ * τ h * (u₀ * h₀)⁻¹ * h⁻¹ = u₀ * τ h * u₀⁻¹ * h⁻¹ := by
      calc u₀ * h₀ * τ h * (u₀ * h₀)⁻¹ * h⁻¹ = u₀ * (h₀ * τ h) * h₀⁻¹ * u₀⁻¹ * h⁻¹ := by group
        _ = u₀ * (τ h * h₀) * h₀⁻¹ * u₀⁻¹ * h⁻¹ := by rw [hcomm]
        _ = u₀ * τ h * u₀⁻¹ * h⁻¹ := by group
    rw [e1] at hc
    have hu1 : h * u₀ * h⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (D.H_le hh) u₀).1 hu₀
    have hmem : τ h * h⁻¹ ∈ U := by
      have e2 : τ h * h⁻¹ = u₀⁻¹ * (u₀ * τ h * u₀⁻¹ * h⁻¹) * (h * u₀ * h⁻¹) := by group
      rw [e2]
      exact U.mul_mem (U.mul_mem (U.inv_mem hu₀) hc) hu1
    exact mul_inv_eq_one.1 (D.U_inf_H _ hmem (H.mul_mem hτh (H.inv_mem hh)))
  rw [D.F_faithful τ hτ hfix, mul_one]
  exact ⟨u₀ * h₀, rfl⟩

theorem burnsideF429a_inner_of_borelAutDiag {Y : Type} [Group Y] {U H : Subgroup Y}
    {F E : Subgroup (MulAut Y)} (D : BorelAutDiag U H F E) (β : MulAut Y)
    (h1 : ∀ x, β x ∈ U ↔ x ∈ U) (h2 : ∀ h ∈ H, β h * h⁻¹ ∈ U) {k : ℕ} (hk : β ^ 2 ^ k = 1) :
    β ∈ (MulAut.conj : Y →* MulAut Y).range := by
  obtain ⟨e, he, σ, hσ, rfl⟩ := D.normal_form β h1
  have hfix : ∀ h ∈ H, σ h = h := by
    intro h hh
    have hσh : σ h ∈ H := D.F_H σ hσ h hh
    have hσhB : σ h ∈ Subgroup.normalizer (U : Set Y) := D.H_le hσh
    have he1 : (σ h)⁻¹ * e (σ h) ∈ U := D.E_triv e he (σ h) hσhB
    have hc : e (σ h) * h⁻¹ ∈ U := by simpa [MulAut.mul_apply] using h2 h hh
    have hu1 : σ h * ((σ h)⁻¹ * e (σ h))⁻¹ * (σ h)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 hσhB _).1 (U.inv_mem he1)
    have hmem : σ h * h⁻¹ ∈ U := by
      have e2 : σ h * h⁻¹ =
          (σ h * ((σ h)⁻¹ * e (σ h))⁻¹ * (σ h)⁻¹) * (e (σ h) * h⁻¹) := by group
      rw [e2]
      exact U.mul_mem hu1 hc
    exact mul_inv_eq_one.1 (D.U_inf_H _ hmem (H.mul_mem hσh (H.inv_mem hh)))
  have hσ1 : σ = 1 := D.F_faithful σ hσ hfix
  subst hσ1
  rw [mul_one] at hk ⊢
  obtain ⟨u, -, hu⟩ := D.E_two e he k hk
  exact ⟨u, hu.symm⟩

theorem burnsideF429a_key_of_model {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {C : Type} [Group C] (Ψ : C ≃* ↥Gp)
    {B U H : Subgroup C} (hB : (M₁ ⊓ M₂).subgroupOf Gp = B.map Ψ.toMonoidHom)
    (hU : pCoreOf 2 B = U) (hH : H ≤ B)
    (hinner : ∀ (β : MulAut C) (k : ℕ), β ^ 2 ^ k = 1 → (∀ x, β x ∈ U ↔ x ∈ U) →
      (∀ h ∈ H, β h * h⁻¹ ∈ U) → β ∈ (MulAut.conj : C →* MulAut C).range) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr k hk hcomm
  set φ : C →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x : C, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = B.map φ := burnsideF429_inf_eq_map Ψ hB
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = U.map φ := by
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, hU]
  have hrX : r ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG r,
        (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hr hxM) ((M₁ ⊓ M₂).inv_mem hr)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG r⁻¹
        simpa [mul_assoc] using this
      · have := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem hr) hxM) hr
        simpa [mul_assoc] using this
  have hrN : r ∈ Subgroup.normalizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hrX
  let β : MulAut C := (Ψ.trans (burnsideF4d_rho Gp r)).trans Ψ.symm
  have hβφ : ∀ x : C, φ (β x) = r * φ x * r⁻¹ := by
    intro x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp r (Ψ x))) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply r (Ψ x)
  have hβpow : β ^ 2 ^ k = 1 := by
    have key : ∀ n : ℕ, β ^ n = (Ψ.trans ((burnsideF4d_rho Gp r) ^ n)).trans Ψ.symm := by
      intro n
      induction n with
      | zero =>
        ext x
        simp
      | succ n ih =>
        ext x
        rw [pow_succ, ih, pow_succ]
        simp [MulAut.mul_apply, β]
    have hρ : (burnsideF4d_rho Gp r) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    rw [key, hρ]
    ext x
    simp
  have hmemU : ∀ x : C, x ∈ U ↔ φ x ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro x
    rw [hS]
    exact (Subgroup.mem_map_iff_mem hφ).symm
  have h1 : ∀ x, β x ∈ U ↔ x ∈ U := by
    intro x
    rw [hmemU, hmemU, hβφ]
    exact ((Subgroup.mem_normalizer_iff.1 hrN) (φ x)).symm
  have h2 : ∀ h ∈ H, β h * h⁻¹ ∈ U := by
    intro h hh
    rw [hmemU, map_mul, map_inv, hβφ]
    have hb : φ h ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      rw [hGB]
      exact ⟨h, hH hh, rfl⟩
    exact hcomm (φ h) hb
  obtain ⟨g, hg⟩ := hinner β k hβpow h1 h2
  have hρ : burnsideF4d_rho Gp r = burnsideF4d_rho Gp ((Ψ g : ↥Gp) : E) := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := Ψ.surjective y
    rw [burnsideF4d_rho_apply, burnsideF4d_rho_apply]
    have e1 := hβφ x
    rw [← hg, MulAut.conj_apply, map_mul, map_mul, map_inv] at e1
    rw [← hφx, ← hφx, ← e1]
  have hr' := burnsideF4d_rho_injective hc hρ
  rw [hr']
  exact (Ψ g).2

end Generic

end CFSG.ASVolI
