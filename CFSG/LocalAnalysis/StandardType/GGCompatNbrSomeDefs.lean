module

public import CFSG.LocalAnalysis.StandardType.GGHypSixRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Abstract

variable {U U' G : Type*} [Group U] [Group U'] [Group G]

theorem ker_comp_le_center_of_injective {ψ : U →* G} (hker : ψ.ker ≤ Subgroup.center U)
    {ι : U' →* U} (hι : Function.Injective ι) : (ψ.comp ι).ker ≤ Subgroup.center U' := by
  intro a ha
  have h1 : ι a ∈ Subgroup.center U := hker (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp ha))
  rw [Subgroup.mem_center_iff]
  intro b
  apply hι
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp h1 (ι b)

variable (Δ : UniversalRootDatum U) (Δ' : UniversalRootDatum U')

theorem ggRootMatch_comp_of_conj {ψ : U →* G} {ι : U' →* U} {δ : Fin Δ'.rank → ℤ}
    {γ : Fin Δ.rank → ℤ} (hroot : ∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ Δ'.rootGroup δ, ι z' = z)
    (htorus : ∀ h' ∈ ggTorus Δ', ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ,
      h * z * h⁻¹ = ι h' * z * (ι h')⁻¹) :
    GGRootMatch Δ Δ' ψ (ψ.comp ι) δ γ 1 := by
  refine ⟨fun z hz => ?_, fun h' hh' => ?_⟩
  · obtain ⟨z', hz', rfl⟩ := hroot z hz
    exact ⟨z', hz', by simp⟩
  · obtain ⟨h, hh, hconj⟩ := htorus h' hh'
    refine ⟨h, hh, fun z hz z' _ heq => ?_⟩
    have e1 : ψ (h * z * h⁻¹) = ψ (ι h' * z * (ι h')⁻¹) := by rw [hconj z hz]
    simp only [MonoidHom.comp_apply, map_mul, map_inv, one_mul, inv_one, mul_one] at heq e1 ⊢
    rw [e1, heq]

theorem ggRootMatch_comp {ψ : U →* G} {ι : U' →* U} {δ : Fin Δ'.rank → ℤ} {γ : Fin Δ.rank → ℤ}
    (hroot : ∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ Δ'.rootGroup δ, ι z' = z)
    (htorus : ∀ h' ∈ ggTorus Δ', ι h' ∈ ggTorus Δ) :
    GGRootMatch Δ Δ' ψ (ψ.comp ι) δ γ 1 :=
  ggRootMatch_comp_of_conj Δ Δ' hroot fun h' hh' => ⟨ι h', htorus h' hh', fun _ _ => rfl⟩

end Abstract

section Compat

theorem ggCompatPresented_comp_of_conj {U G : Type*} [Group U] [Group G]
    {Δ : UniversalRootDatum U} {ψ : U →* G} (hker : ψ.ker ≤ Subgroup.center U)
    {t' : StatedLieTag} {n' f' : ℕ} (hadm : StatedLieAdmissible t' n' 2 f')
    (hrk : 2 ≤ (ggU t' n' f').D.rank) {ι : (ggU t' n' f').K →* U} (hι : Function.Injective ι)
    {δ : Fin (ggU t' n' f').D.rank → ℤ} (hδ : δ ∈ (ggU t' n' f').D.roots)
    {γ : Fin Δ.rank → ℤ} (hγ : γ ∈ Δ.roots)
    (hroot : ∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ (ggU t' n' f').D.rootGroup δ, ι z' = z)
    (htorus : ∀ h' ∈ ggTorus (ggU t' n' f').D, ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ,
      h * z * h⁻¹ = ι h' * z * (ι h')⁻¹) :
    GGCompatPresented Δ ψ (ψ.comp ι).range :=
  ⟨t', n', f', ψ.comp ι, hadm, hrk, ker_comp_le_center_of_injective hker hι, rfl, δ, hδ, γ, hγ,
    1, ggRootMatch_comp_of_conj Δ _ hroot htorus⟩

theorem ggCompatPresented_comp {U G : Type*} [Group U] [Group G] {Δ : UniversalRootDatum U}
    {ψ : U →* G} (hker : ψ.ker ≤ Subgroup.center U) {t' : StatedLieTag} {n' f' : ℕ}
    (hadm : StatedLieAdmissible t' n' 2 f') (hrk : 2 ≤ (ggU t' n' f').D.rank)
    {ι : (ggU t' n' f').K →* U} (hι : Function.Injective ι)
    {δ : Fin (ggU t' n' f').D.rank → ℤ} (hδ : δ ∈ (ggU t' n' f').D.roots)
    {γ : Fin Δ.rank → ℤ} (hγ : γ ∈ Δ.roots)
    (hroot : ∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ (ggU t' n' f').D.rootGroup δ, ι z' = z)
    (htorus : ∀ h' ∈ ggTorus (ggU t' n' f').D, ι h' ∈ ggTorus Δ) :
    GGCompatPresented Δ ψ (ψ.comp ι).range :=
  ggCompatPresented_comp_of_conj hker hadm hrk hι hδ hγ hroot fun h' hh' =>
    ⟨ι h', htorus h' hh', fun _ _ => rfl⟩

@[expose] def GGSecFiveCompat {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  ∃ (t₀ : StatedLieTag) (n₀ f₀ : ℕ) (ψ₀ : (ggU t₀ n₀ f₀).K →* G),
    GGPresentsG0 (ggG0 p B x L D J) (ggU t₀ n₀ f₀).D t₀ n₀ f₀ ψ₀ ∧
      ∃ K : Subgroup G, (K = L ∨ ∃ y : G, GGNbr p B x D J y K) ∧
        GGCompatPresented (ggU t₀ n₀ f₀).D ψ₀ K

end Compat

end CFSG.StandardType
