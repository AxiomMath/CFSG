module

public import CFSG.Milestones.ASVolI.F429.Base

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

theorem burnsideF429a_mem_of_model₂ {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {C : Type} [Group C] (Ψ : C ≃* ↥Gp)
    {P₁ P₂ : Subgroup C} (h₁ : M₁.subgroupOf Gp = P₁.map Ψ.toMonoidHom)
    (h₂ : M₂.subgroupOf Gp = P₂.map Ψ.toMonoidHom) {r : E} (hr : r ∈ M₁ ⊓ M₂)
    (hinner : ∀ β : MulAut C, (∀ x, β x ∈ P₁ ↔ x ∈ P₁) → (∀ x, β x ∈ P₂ ↔ x ∈ P₂) →
      (∀ x : C, ((Ψ (β x) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹) →
      β ∈ (MulAut.conj : C →* MulAut C).range) : r ∈ Gp := by
  set φ : C →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x : C, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hG₁ : Gp ⊓ M₁ = P₁.map φ := burnsideF429_inf_eq_map Ψ h₁
  have hG₂ : Gp ⊓ M₂ = P₂.map φ := burnsideF429_inf_eq_map Ψ h₂
  let β : MulAut C := (Ψ.trans (burnsideF4d_rho Gp r)).trans Ψ.symm
  have hβφ : ∀ x : C, φ (β x) = r * φ x * r⁻¹ := by
    intro x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp r (Ψ x))) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply r (Ψ x)
  have hnorm : ∀ M : Subgroup E, r ∈ M → ∀ y : E, y ∈ Gp ⊓ M ↔ r * y * r⁻¹ ∈ Gp ⊓ M := by
    intro M hM y
    constructor
    · rintro ⟨hyG, hyM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem y hyG r,
        M.mul_mem (M.mul_mem hM hyM) (M.inv_mem hM)⟩
    · rintro ⟨hyG, hyM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hyG r⁻¹
        simpa [mul_assoc] using this
      · have := M.mul_mem (M.mul_mem (M.inv_mem hM) hyM) hM
        simpa [mul_assoc] using this
  have hstab : ∀ (P : Subgroup C) (M : Subgroup E), Gp ⊓ M = P.map φ → r ∈ M →
      ∀ x, β x ∈ P ↔ x ∈ P := by
    intro P M hPM hM x
    have e1 : β x ∈ P ↔ φ (β x) ∈ P.map φ := (Subgroup.mem_map_iff_mem hφ).symm
    have e2 : x ∈ P ↔ φ x ∈ P.map φ := (Subgroup.mem_map_iff_mem hφ).symm
    rw [e1, e2, ← hPM, hβφ]
    exact (hnorm M hM (φ x)).symm
  obtain ⟨g, hg⟩ := hinner β (hstab P₁ M₁ hG₁ hr.1) (hstab P₂ M₂ hG₂ hr.2) hβφ
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

theorem burnsideF429a_pow_eq_one_of_intertwine {E : Type} [Group E] {Gp : Subgroup E}
    {C : Type} [Group C] (Ψ : C ≃* ↥Gp) {β : MulAut C} {r : E}
    (h : ∀ x : C, ((Ψ (β x) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹) {n : ℕ}
    (hn : r ^ n = 1) : β ^ n = 1 := by
  have key : ∀ m : ℕ, ∀ x : C,
      ((Ψ ((β ^ m) x) : ↥Gp) : E) = r ^ m * ((Ψ x : ↥Gp) : E) * (r ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, h, ih, pow_succ']
      group
  refine MulEquiv.ext fun x => ?_
  apply Ψ.injective
  apply Subtype.ext
  rw [key n x, hn]
  simp

end Generic

end CFSG.ASVolI
