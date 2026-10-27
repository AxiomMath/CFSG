module

public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Abstract

variable {U U' G : Type*} [Group U] [Group U'] [Group G]
variable (Δ : UniversalRootDatum U) (Δ' : UniversalRootDatum U')

theorem ggRootMatch_conj_comp {ψ : U →* G} {ι : U' →* U} (u : U) {δ : Fin Δ'.rank → ℤ}
    {γ : Fin Δ.rank → ℤ} (hroot : ∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ Δ'.rootGroup δ, ι z' = z)
    (htorus : ∀ h' ∈ ggTorus Δ', ι h' ∈ ggTorus Δ) :
    GGRootMatch Δ Δ' ψ (ψ.comp ((MulAut.conj u).toMonoidHom.comp ι)) δ γ u := by
  have hcomp : ∀ x : U',
      (ψ.comp ((MulAut.conj u).toMonoidHom.comp ι)) x = ψ (u * ι x * u⁻¹) := by
    intro x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    change ψ ((MulAut.conj u) (ι x)) = ψ (u * ι x * u⁻¹)
    rw [MulAut.conj_apply]
  refine ⟨fun z hz => ?_, fun h' hh' => ?_⟩
  · obtain ⟨z', hz', rfl⟩ := hroot z hz
    exact ⟨z', hz', hcomp z'⟩
  · refine ⟨ι h', htorus h' hh', fun z hz z' hz' heq => ?_⟩
    rw [hcomp] at heq
    have hmap : ∀ a b : U, ψ (a * b * a⁻¹) = ψ a * ψ b * (ψ a)⁻¹ := by
      intro a b; rw [map_mul, map_mul, map_inv]
    have hX : u * ι (h' * z' * h'⁻¹) * u⁻¹
        = (u * ι h' * u⁻¹) * (u * ι z' * u⁻¹) * (u * ι h' * u⁻¹)⁻¹ := by
      simp only [map_mul, map_inv]; group
    have hZ : u * (ι h' * z * (ι h')⁻¹) * u⁻¹
        = (u * ι h' * u⁻¹) * (u * z * u⁻¹) * (u * ι h' * u⁻¹)⁻¹ := by
      group
    rw [hcomp, hX, hZ]
    conv_lhs => rw [hmap]
    conv_rhs => rw [hmap]
    rw [heq]

end Abstract

section Compat

theorem ggCompatPresented_conj_comp {U G : Type*} [Group U] [Group G] {Δ : UniversalRootDatum U}
    {ψ : U →* G} (hker : ψ.ker ≤ Subgroup.center U) {t' : StatedLieTag} {n' f' : ℕ}
    (hadm : StatedLieAdmissible t' n' 2 f') (hrk : 2 ≤ (ggU t' n' f').D.rank)
    {ι : (ggU t' n' f').K →* U} (hι : Function.Injective ι) (u : U)
    {δ : Fin (ggU t' n' f').D.rank → ℤ} (hδ : δ ∈ (ggU t' n' f').D.roots)
    {γ : Fin Δ.rank → ℤ} (hγ : γ ∈ Δ.roots)
    (hroot : ∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ (ggU t' n' f').D.rootGroup δ, ι z' = z)
    (htorus : ∀ h' ∈ ggTorus (ggU t' n' f').D, ι h' ∈ ggTorus Δ) :
    GGCompatPresented Δ ψ (ψ.comp ((MulAut.conj u).toMonoidHom.comp ι)).range :=
  ⟨t', n', f', ψ.comp ((MulAut.conj u).toMonoidHom.comp ι), hadm, hrk,
    ker_comp_le_center_of_injective hker ((MulAut.conj u).injective.comp hι), rfl, δ, hδ, γ, hγ,
    u, ggRootMatch_conj_comp Δ _ u hroot htorus⟩

end Compat

end CFSG.StandardType

end
