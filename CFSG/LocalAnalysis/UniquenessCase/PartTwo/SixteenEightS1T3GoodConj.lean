module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped Matrix

theorem s16t3_good_conj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {H F₀ : Subgroup (Matrix.GeneralLinearGroup ι K)} (hF₀ : F₀ ≤ H) (hp : IsPGroup 3 ↥F₀)
    (hc : ¬ IsCyclic ↥F₀) {x₀ x : ι → K}
    (hfix : ∀ f ∈ F₀, ((f : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec x₀ = x₀)
    {g : Matrix.GeneralLinearGroup ι K} (hg : g ∈ H)
    (hgx : ((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec x₀ = x) :
    ∃ F : Subgroup ↥H, IsPGroup 3 ↥F ∧ ¬ IsCyclic ↥F ∧
      ∀ γ ∈ F, ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec x = x := by
  classical
  let c : Matrix.GeneralLinearGroup ι K →* Matrix.GeneralLinearGroup ι K :=
    (MulAut.conj g).toMonoidHom
  let F₁ : Subgroup (Matrix.GeneralLinearGroup ι K) := F₀.map c
  have hF₁H : F₁ ≤ H := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    simp only [c, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact H.mul_mem (H.mul_mem hg (hF₀ hf)) (H.inv_mem hg)
  let F : Subgroup ↥H := F₁.subgroupOf H
  refine ⟨F, ?_, ?_, ?_⟩
  · have h₁ : IsPGroup 3 F₁ := hp.map c
    exact h₁.of_equiv (Subgroup.subgroupOfEquivOfLe hF₁H).symm
  · intro hcyc
    let e : ↥F ≃* ↥F₀ :=
      (Subgroup.subgroupOfEquivOfLe hF₁H).trans
        (Subgroup.equivMapOfInjective F₀ c (MulAut.conj g).injective).symm
    exact hc (isCyclic_of_surjective e.toMonoidHom e.surjective)
  · intro γ hγ
    have hγ₁ : (γ : Matrix.GeneralLinearGroup ι K) ∈ F₁ := Subgroup.mem_subgroupOf.mp hγ
    rw [Subgroup.mem_map] at hγ₁
    obtain ⟨f, hf, hfg⟩ := hγ₁
    have h1 : ((g⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ x = x₀ := by
      rw [← hgx, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hγeq : (γ : Matrix.GeneralLinearGroup ι K) = g * f * g⁻¹ := by
      rw [← hfg]
      simp only [c, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hγeq, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      h1, hfix f hf, hgx]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
