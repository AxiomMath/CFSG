module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactor

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.CommonFactorJoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.StandardType.LieCore

open CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {Ω : Type} [Field Ω]

theorem ratOrbit_subset_of_common_selected
    {M : Type*} [CommGroup M]
    {χD : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {χe : Multiplicative (Fin Tag.F4.rank → ℤ) →* Ωˣ}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    (i : KernelComponent χD) (j : KernelComponent χe)
    {Jg K : Subgroup (ModGL Tag.F4 Ω)}
    (hker : kernelRoots χD ⊆ kernelRoots χe)
    (hJ : Jg ≤ rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots χD i)))
    (hK : Jg ≤ K)
    (hKspan : K ≤ rootSpan Tag.F4 Ω (rationalRoots ρ χe j))
    (hJnonabel : ∃ y ∈ Jg, ∃ z ∈ Jg, y * z ≠ z * y)
    (hcomm : ∀ {k l : KernelComponent χe}, rationalRoots ρ χe k ≠ rationalRoots ρ χe l →
      ∀ x ∈ rootSpan Tag.F4 Ω (rationalRoots ρ χe k),
      ∀ y ∈ rootSpan Tag.F4 Ω (rationalRoots ρ χe l), Commute x y) :
    ratOrbit (fun u => ρ u) (componentRoots χD i) ⊆ rationalRoots ρ χe j := by
  classical
  obtain ⟨α, hαi⟩ := Quotient.exists_rep i
  have hαmem : (α : Fin Tag.F4.rank → ℤ) ∈ componentRoots χD i := ⟨α.2, hαi⟩
  let k : KernelComponent χe := ⟦⟨α.1, hker α.2⟩⟧
  have hαk : (α : Fin Tag.F4.rank → ℤ) ∈ componentRoots χe k := ⟨hker α.2, rfl⟩
  have hsub : componentRoots χD i ⊆ componentRoots χe k :=
    CFSG.StandardType.TableCRes.componentRoots_subset_of_kernel_subset hker hαmem hαk
  have hrat : ratOrbit (fun u => ρ u) (componentRoots χD i) ⊆ rationalRoots ρ χe k := by
    rintro γ ⟨n, δ, hδ, rfl⟩
    exact ⟨n, δ, hsub hδ, rfl⟩
  have hJk : Jg ≤ rootSpan Tag.F4 Ω (rationalRoots ρ χe k) :=
    hJ.trans (CFSG.LieType.Chevalley.rootSpan_mono hrat)
  have heq : rationalRoots ρ χe k = rationalRoots ρ χe j := by
    by_contra hne
    obtain ⟨y, hy, z, hz, hyz⟩ := hJnonabel
    exact hyz (hcomm (k := k) (l := j) hne y (hJk hy) z (hKspan (hK hz)))
  intro γ hγ
  exact heq ▸ hrat hγ

theorem ratOrbit_subset_componentRoots_of_common_selected
    {M : Type*} [CommGroup M]
    {χD : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {χe : Multiplicative (Fin Tag.F4.rank → ℤ) →* Ωˣ}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    (i : KernelComponent χD) (j : KernelComponent χe)
    {Jg K : Subgroup (ModGL Tag.F4 Ω)}
    (hker : kernelRoots χD ⊆ kernelRoots χe)
    (hJ : Jg ≤ rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots χD i)))
    (hK : Jg ≤ K)
    (hKspan : K ≤ rootSpan Tag.F4 Ω (rationalRoots ρ χe j))
    (hJnonabel : ∃ y ∈ Jg, ∃ z ∈ Jg, y * z ≠ z * y)
    (hcomm : ∀ {k l : KernelComponent χe}, rationalRoots ρ χe k ≠ rationalRoots ρ χe l →
      ∀ x ∈ rootSpan Tag.F4 Ω (rationalRoots ρ χe k),
      ∀ y ∈ rootSpan Tag.F4 Ω (rationalRoots ρ χe l), Commute x y)
    (horbit1 : componentOrbitLength ρ (componentRoots χe j) = 1) :
    ratOrbit (fun u => ρ u) (componentRoots χD i) ⊆ componentRoots χe j := by
  intro γ hγ
  have h2 : γ ∈ rationalRoots ρ χe j :=
    ratOrbit_subset_of_common_selected i j hker hJ hK hKspan hJnonabel hcomm hγ
  rwa [CommonFactor.rationalRoots_eq_componentRoots_of_orbitLength_one
    j horbit1] at h2

theorem componentRoots_subset_of_common_selected
    {M : Type*} [CommGroup M]
    {χD : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {χe : Multiplicative (Fin Tag.F4.rank → ℤ) →* Ωˣ}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    (i : KernelComponent χD) (j : KernelComponent χe)
    {Jg K : Subgroup (ModGL Tag.F4 Ω)}
    (hker : kernelRoots χD ⊆ kernelRoots χe)
    (hJ : Jg ≤ rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots χD i)))
    (hK : Jg ≤ K)
    (hKspan : K ≤ rootSpan Tag.F4 Ω (rationalRoots ρ χe j))
    (hJnonabel : ∃ y ∈ Jg, ∃ z ∈ Jg, y * z ≠ z * y)
    (hcomm : ∀ {k l : KernelComponent χe}, rationalRoots ρ χe k ≠ rationalRoots ρ χe l →
      ∀ x ∈ rootSpan Tag.F4 Ω (rationalRoots ρ χe k),
      ∀ y ∈ rootSpan Tag.F4 Ω (rationalRoots ρ χe l), Commute x y)
    (horbit1 : componentOrbitLength ρ (componentRoots χe j) = 1) :
    componentRoots χD i ⊆ componentRoots χe j := by
  intro γ hγ
  exact ratOrbit_subset_componentRoots_of_common_selected i j hker hJ hK hKspan hJnonabel hcomm
    horbit1 ⟨0, γ, hγ, rfl⟩

end CFSG.StandardType.F4ExplicitPos.CommonFactorJoint

end

end
