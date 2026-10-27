module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CyclicFinish
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactorJoint

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CommonPairTransport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.LieCore

variable {Ω : Type} [Field Ω]

theorem componentRoots_subset_of_common_selected_joint
    {M : Type*} [CommGroup M]
    {χD : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {χe : Multiplicative (Fin Tag.F4.rank → ℤ) →* Ωˣ}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    (i : KernelComponent χD) (j : KernelComponent χe)
    {Jg K : Subgroup (ModGL Tag.F4 Ω)}
    (hker : kernelRoots χD ⊆ kernelRoots χe)
    (hkerρ : ∀ γ ∈ kernelRoots χe, ρ γ ∈ kernelRoots χe)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (hJ : Jg ≤ rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots χD i)))
    (hK : Jg ≤ K)
    (hKspan : K ≤ rootSpan Tag.F4 Ω (rationalRoots ρ χe j))
    (hJnonabel : ∃ y ∈ Jg, ∃ z ∈ Jg, y * z ≠ z * y)
    (horbit1 : componentOrbitLength ρ (componentRoots χe j) = 1) :
    componentRoots χD i ⊆ componentRoots χe j :=
  CommonFactorJoint.componentRoots_subset_of_common_selected i j hker hJ hK hKspan
    hJnonabel
    (fun {k l} hkl x hx y hy =>
      CyclicFinish.f4_orbit_commute_rootSpan_rationalRoots hkerρ hform hkl x hx y hy)
    horbit1

theorem rootSubgroup_le_componentRootSpan_of_mem_componentRoots
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {α : Fin Tag.F4.rank → ℤ} {i : KernelComponent χ}
    (hα : α ∈ componentRoots χ i) :
    rootSubgroup Tag.F4 Ω α ≤ componentRootSpan Ω χ i := by
  obtain ⟨hk, hi⟩ := hα
  intro x hx
  exact hi ▸ rootSubgroup_le_componentRootSpan (χ := χ) (K := Ω)
    (⟨α, hk⟩ : kernelRoots χ) hx

end CFSG.StandardType.F4ExplicitPos.CommonPairTransport

end

end
