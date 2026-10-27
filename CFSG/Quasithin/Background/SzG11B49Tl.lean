module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

namespace CFSG.Quasithin.G11.SzG11S

open CFSG.GroupTheory.GLnTwoSplitting
  (exists_comp_eq_of_apply_eq_zero exists_dual_eq_one_of_notMem exists_transvection_apply_eq
    transvection_apply two_add_eq_iff two_add_self zmod_two_eq_zero_or_one)

namespace B49Aux

theorem comp_equiv_inj {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (g : W ≃ₗ[ZMod 2] W) {φ ψ : Module.Dual (ZMod 2) W}
    (h : φ ∘ₗ (g : W →ₗ[ZMod 2] W) = ψ ∘ₗ (g : W →ₗ[ZMod 2] W)) : φ = ψ :=
  (LinearMap.cancel_right g.surjective).1 h

theorem comp_equiv_ne_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (g : W ≃ₗ[ZMod 2] W) {φ : Module.Dual (ZMod 2) W} (h : φ ≠ 0) :
    φ ∘ₗ (g : W →ₗ[ZMod 2] W) ≠ 0 :=
  fun h0 => h (comp_equiv_inj g (h0.trans (LinearMap.zero_comp _).symm))

theorem coe_mul_eq_comp {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (g h : W ≃ₗ[ZMod 2] W) :
    ((g * h : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
      (g : W →ₗ[ZMod 2] W) ∘ₗ (h : W →ₗ[ZMod 2] W) :=
  rfl

theorem exists_vec_of_notMem_span {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {φ χ ψ : Module.Dual (ZMod 2) W}
    (h : ψ ∉ Submodule.span (ZMod 2) {φ, χ}) :
    ∃ d : W, φ d = 0 ∧ χ d = 0 ∧ ψ d = 1 := by
  obtain ⟨Φ, hΦ, hΦψ⟩ := exists_dual_eq_one_of_notMem h
  refine ⟨(Module.evalEquiv (ZMod 2) W).symm Φ, ?_, ?_, ?_⟩
  · rw [Module.apply_evalEquiv_symm_apply]
    exact hΦ φ (Submodule.subset_span (by simp))
  · rw [Module.apply_evalEquiv_symm_apply]
    exact hΦ χ (Submodule.subset_span (by simp))
  · rw [Module.apply_evalEquiv_symm_apply]
    exact hΦψ

theorem exists_equiv_of_two_forms {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {z : W} {φ₁ φ₂ ψ : Module.Dual (ZMod 2) W}
    (h₂ : φ₂ ≠ 0) (h₁₂ : φ₁ ≠ φ₂) (hψ : ψ ≠ 0) (hψ₁ : ψ ≠ φ₁)
    (hz₂ : φ₂ z = 0) (hzψ : ψ z = 0) :
    ∃ g : W ≃ₗ[ZMod 2] W, g z = z ∧ φ₁ ∘ₗ (g : W →ₗ[ZMod 2] W) = φ₁ ∧
      ψ ∘ₗ (g : W →ₗ[ZMod 2] W) = φ₂ := by
  by_cases hψ₂ : ψ = φ₂
  · exact ⟨1, rfl, rfl, by rw [hψ₂]; rfl⟩
  have hnot : ψ ∉ Submodule.span (ZMod 2) {φ₁, ψ + φ₂} := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hmem
    rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b with rfl | rfl
    · rw [zero_smul, zero_smul, add_zero] at hab
      exact hψ hab.symm
    · rw [zero_smul, one_smul, zero_add] at hab
      exact h₂ (add_left_cancel (hab.trans (add_zero ψ).symm))
    · rw [one_smul, zero_smul, add_zero] at hab
      exact hψ₁ hab.symm
    · rw [one_smul, one_smul] at hab
      have h' : ψ + (φ₁ + φ₂) = ψ + 0 :=
        ((add_left_comm ψ φ₁ φ₂).trans hab).trans (add_zero ψ).symm
      exact h₁₂ ((two_add_eq_iff.1 (add_left_cancel h')).trans (zero_add φ₂))
  obtain ⟨d, hd₁, hdχ, hdψ⟩ := exists_vec_of_notMem_span hnot
  have hχz : (ψ + φ₂) z = 0 := by rw [LinearMap.add_apply, hzψ, hz₂, add_zero]
  refine ⟨LinearEquiv.transvection hdχ, ?_, ?_, ?_⟩
  · rw [transvection_apply, hχz, zero_smul, add_zero]
  · refine LinearMap.ext fun x => ?_
    change φ₁ (LinearEquiv.transvection hdχ x) = φ₁ x
    rw [transvection_apply, map_add, map_smul, hd₁, smul_zero, add_zero]
  · refine LinearMap.ext fun x => ?_
    change ψ (LinearEquiv.transvection hdχ x) = φ₂ x
    rw [transvection_apply, map_add, map_smul, hdψ, smul_eq_mul, mul_one, LinearMap.add_apply,
      ← add_assoc, two_add_self, zero_add]

theorem exists_equiv_triple_of_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {z : W} {φ₁ φ₂ φ₁' φ₂' : Module.Dual (ZMod 2) W}
    (h₁ : φ₁ ≠ 0) (h₂ : φ₂ ≠ 0) (h₁₂ : φ₁ ≠ φ₂)
    (h₁' : φ₁' ≠ 0) (h₂' : φ₂' ≠ 0) (h₁₂' : φ₁' ≠ φ₂')
    (hz₁ : φ₁ z = 0) (hz₂ : φ₂ z = 0) (hz₁' : φ₁' z = 0) (hz₂' : φ₂' z = 0) :
    ∃ g : W ≃ₗ[ZMod 2] W, g z = z ∧ φ₁' ∘ₗ (g : W →ₗ[ZMod 2] W) = φ₁ ∧
      φ₂' ∘ₗ (g : W →ₗ[ZMod 2] W) = φ₂ := by
  obtain ⟨g₁, hg₁z, hg₁⟩ := exists_comp_eq_of_apply_eq_zero h₁' h₁ hz₁' hz₁
  have hψ0 : φ₂' ∘ₗ (g₁ : W →ₗ[ZMod 2] W) ≠ 0 := comp_equiv_ne_zero g₁ h₂'
  have hψ1 : φ₂' ∘ₗ (g₁ : W →ₗ[ZMod 2] W) ≠ φ₁ :=
    fun h => h₁₂' (comp_equiv_inj g₁ (h.trans hg₁.symm)).symm
  have hψz : (φ₂' ∘ₗ (g₁ : W →ₗ[ZMod 2] W)) z = 0 := by
    change φ₂' (g₁ z) = 0
    rw [hg₁z, hz₂']
  obtain ⟨g₂, hg₂z, hg₂₁, hg₂₂⟩ := exists_equiv_of_two_forms h₂ h₁₂ hψ0 hψ1 hz₂ hψz
  refine ⟨g₁ * g₂, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hg₂z, hg₁z]
  · rw [coe_mul_eq_comp, ← LinearMap.comp_assoc, hg₁, hg₂₁]
  · rw [coe_mul_eq_comp, ← LinearMap.comp_assoc, hg₂₂]

theorem exists_equiv_triple {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {z z' : W} (hz : z ≠ 0) (hz' : z' ≠ 0)
    {φ₁ φ₂ φ₁' φ₂' : Module.Dual (ZMod 2) W}
    (h₁ : φ₁ ≠ 0) (h₂ : φ₂ ≠ 0) (h₁₂ : φ₁ ≠ φ₂)
    (h₁' : φ₁' ≠ 0) (h₂' : φ₂' ≠ 0) (h₁₂' : φ₁' ≠ φ₂')
    (hz₁ : φ₁ z = 0) (hz₂ : φ₂ z = 0) (hz₁' : φ₁' z' = 0) (hz₂' : φ₂' z' = 0) :
    ∃ g : W ≃ₗ[ZMod 2] W, g z = z' ∧ φ₁' ∘ₗ (g : W →ₗ[ZMod 2] W) = φ₁ ∧
      φ₂' ∘ₗ (g : W →ₗ[ZMod 2] W) = φ₂ := by
  obtain ⟨f, d, hfd, hfz⟩ := exists_transvection_apply_eq hz hz'
  generalize LinearEquiv.transvection hfd = t at hfz
  obtain ⟨g, hgz, hg₁, hg₂⟩ := exists_equiv_triple_of_eq (z := z) h₁ h₂ h₁₂
    (comp_equiv_ne_zero t h₁') (comp_equiv_ne_zero t h₂') (fun h => h₁₂' (comp_equiv_inj t h))
    hz₁ hz₂ (by change φ₁' (t z) = 0; rw [hfz, hz₁']) (by change φ₂' (t z) = 0; rw [hfz, hz₂'])
  refine ⟨t * g, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hgz, hfz]
  · rw [coe_mul_eq_comp, ← LinearMap.comp_assoc]
    exact hg₁
  · rw [coe_mul_eq_comp, ← LinearMap.comp_assoc]
    exact hg₂

end B49Aux

end CFSG.Quasithin.G11.SzG11S
