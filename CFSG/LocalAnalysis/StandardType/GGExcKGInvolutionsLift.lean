module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGLatOrth

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

theorem ggInvolution_conj_mem_of_factor {U A G : Type*} [Group U] [Group A] [Group G]
    (ψ : U →* G) (φ : U →* A) (χ : A →* G) (hχ : Function.Injective χ)
    (hφ : Function.Surjective φ) (hψ : ∀ u, χ (φ u) = ψ u)
    (ℛ : Set (Subgroup U)) (rep : Set A)
    (hrep : ∀ r ∈ rep, ∃ R ∈ ℛ, ∃ r' ∈ R, φ r' = r)
    (hclass : ∀ y : A, orderOf y = 2 → ∃ a : A, a * y * a⁻¹ ∈ rep)
    {s : G} (hs : s ∈ ψ.range) (hs2 : orderOf s = 2) :
    ∃ g ∈ ψ.range, ∃ R ∈ ℛ, g * s * g⁻¹ ∈ R.map ψ := by
  obtain ⟨u, rfl⟩ := hs
  have hy2 : orderOf (φ u) = 2 := by
    rw [← orderOf_injective χ hχ (φ u), hψ u]
    exact hs2
  obtain ⟨a, ha⟩ := hclass (φ u) hy2
  obtain ⟨R, hR, r', hr', hφr'⟩ := hrep (a * φ u * a⁻¹) ha
  obtain ⟨ã, rfl⟩ := hφ a
  refine ⟨ψ ã, ⟨ã, rfl⟩, R, hR, ?_⟩
  rw [Subgroup.mem_map]
  refine ⟨r', hr', ?_⟩
  rw [← hψ r', hφr']
  simp only [map_mul, map_inv, hψ]

section InvolutionsLift


theorem ggExcKGInvolutions_of_factor (t : StatedLieTag) (n f : ℕ) {G : Type} [Group G]
    (ψ : (ggU t n f).K →* G) {A : Type} [Group A] (φ : (ggU t n f).K →* A) (χ : A →* G)
    (hχ : Function.Injective χ) (hφ : Function.Surjective φ) (hψ : ∀ u, χ (φ u) = ψ u)
    (rep : Set A)
    (hrep : ∀ r ∈ rep, ∃ Z : Set (Fin (ggU t n f).D.rank → ℤ), ggASClass t n f Z ∧
      ∃ r' ∈ ⨆ β ∈ Z, (ggU t n f).D.rootGroup β, φ r' = r)
    (hclass : ∀ y : A, orderOf y = 2 → ∃ a : A, a * y * a⁻¹ ∈ rep)
    {s : G} (hs : s ∈ ψ.range) (hs2 : orderOf s = 2) :
    ∃ g ∈ ψ.range, ∃ Z : Set (Fin (ggU t n f).D.rank → ℤ), ggASClass t n f Z ∧
      g * s * g⁻¹ ∈ ⨆ β ∈ Z, ((ggU t n f).D.rootGroup β).map ψ := by
  let ℛ : Set (Subgroup (ggU t n f).K) :=
    {R | ∃ Z : Set (Fin (ggU t n f).D.rank → ℤ), ggASClass t n f Z ∧
      R = ⨆ β ∈ Z, (ggU t n f).D.rootGroup β}
  have hrep' : ∀ r ∈ rep, ∃ R ∈ ℛ, ∃ r' ∈ R, φ r' = r := by
    intro r hr
    obtain ⟨Z, hZ, r', hr', hφr'⟩ := hrep r hr
    exact ⟨⨆ β ∈ Z, (ggU t n f).D.rootGroup β, ⟨Z, hZ, rfl⟩, r', hr', hφr'⟩
  obtain ⟨g, hg, R, hR, hmem⟩ :=
    ggInvolution_conj_mem_of_factor ψ φ χ hχ hφ hψ ℛ rep hrep' hclass hs hs2
  obtain ⟨Z, hZ, hRZ⟩ := hR
  refine ⟨g, hg, Z, hZ, ?_⟩
  rw [hRZ] at hmem
  simpa only [Subgroup.map_iSup] using hmem

end InvolutionsLift

end CFSG.StandardType
