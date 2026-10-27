module

public import CFSG.LieType.Chevalley.SignKernelStabilizer

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {M : Type*}
  [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

private theorem rootReflection_smul_mem_componentRoots_classStab {β : Fin τ.rank → ℤ}
    (hβ : β ∈ kernelRoots χ) {i : KernelComponent χ} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots χ i) : rootReflection β • γ ∈ componentRoots χ i := by
  by_cases h0 : iform β γ = 0
  · rw [rootReflection_smul_of_iform_eq_zero hβ.1 h0]
    exact hγ
  have hk : rootReflection β • γ ∈ kernelRoots χ :=
    smul_mem_kernelRoots (rootReflection_mem_charStabilizer hβ) hγ.1
  have h1 : iform (rootReflection β • γ) β ≠ 0 := by
    have e := iform_smul (rootReflection β) γ β
    rw [rootReflection_smul_self hβ.1, ← neg_one_smul ℤ β, iform_smul_right] at e
    intro h
    apply h0
    rw [iform_comm, ← e, h, mul_zero]
  have e1 : (⟦⟨_, hk⟩⟧ : KernelComponent χ) = ⟦⟨β, hβ⟩⟧ := mk_eq_of_iform_ne_zero h1
  have e2 : (⟦⟨β, hβ⟩⟧ : KernelComponent χ) = ⟦⟨γ, hγ.1⟩⟧ := mk_eq_of_iform_ne_zero h0
  exact ⟨hk, e1.trans (e2.trans hγ.2)⟩

theorem smul_mem_componentRoots_of_mem_kernelWeylGroup {i : KernelComponent χ}
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots χ i) {w : WeylGroup τ}
    (hw : w ∈ kernelWeylGroup χ) : w • γ ∈ componentRoots χ i := by
  revert γ
  induction hw using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨v, j, hα, rfl⟩ := hx
    intro γ hγ
    rw [conj_simple_eq_rootReflection]
    exact rootReflection_smul_mem_componentRoots_classStab hα hγ
  | inv_mem x hx =>
    obtain ⟨v, j, hα, rfl⟩ := hx
    intro γ hγ
    rw [conj_simple_eq_rootReflection, rootReflection_inv hα.1]
    exact rootReflection_smul_mem_componentRoots_classStab hα hγ
  | one => exact fun hγ => by rwa [one_smul]
  | mul x y _ _ hx hy => exact fun hγ => by rw [mul_smul]; exact hx (hy hγ)

end CFSG.StandardType.SCFourCover
