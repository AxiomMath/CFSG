module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCForm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCLev

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62

theorem s16c1c_card_le_model {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} (hP : P ≤ O₀ true)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h2 : ∀ x ∈ P, x ^ 2 = 1) :
    Nat.card P ≤ 16 := by
  have hp : IsPGroup 2 P := fun x => ⟨1, by
    apply Subtype.ext
    simpa using h2 x x.2⟩
  obtain ⟨g, -, hconj⟩ := s16c1c_exists_conj_mem_T hP hp
  set φ : (V₀ ≃ₗ[ZMod 2] V₀) →* (V₀ ≃ₗ[ZMod 2] V₀) := (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hφapply : ∀ x, φ x = g⁻¹ * x * g := fun x => by simp [hφ, MulAut.conj_apply]
  have hφinj : Function.Injective φ := (MulAut.conj g⁻¹).injective
  have hcard : Nat.card (P.map φ) = Nat.card P := Subgroup.card_map_of_injective hφinj
  rw [← hcard]
  refine s16c1c_card_le_of_codes ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hab a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h2 a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩
    exact s16c1c_exists_coded_of_mem_T (by rw [hφapply]; exact hconj a ha)

theorem s16c1c_rankLe4 {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaRankLe4 H := by
  intro E hEN hEab
  let κe : (V₀ ≃ₗ[ZMod 2] V₀) ≃* MulAut W :=
    MulEquiv.ofBijective (s16c1G_kappa β)
      ⟨s16c1G_kappa_injective β, s16c1G44_kappa_surjective β⟩
  let E' : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := E.comap κe.toMonoidHom
  have hmemE' : ∀ g, g ∈ E' ↔ s16c1G_kappa β g ∈ E := fun g => Iff.rfl
  have hcard : Nat.card E' = Nat.card E := by
    have h1 : E' = E.map κe.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm κe E
    rw [h1]
    exact Subgroup.card_map_of_injective κe.symm.injective
  rw [← hcard]
  refine s16c1c_card_le_model ?_ ?_ ?_
  · intro g hg
    exact s16c1c_mem_O_of_mem_normalizer hβ (hEN ((hmemE' g).1 hg))
  · intro g hg k hk
    apply s16c1G_kappa_injective β
    rw [map_mul, map_mul]
    exact hEab.1 _ ((hmemE' g).1 hg) _ ((hmemE' k).1 hk)
  · intro g hg
    apply s16c1G_kappa_injective β
    rw [map_pow, map_one]
    exact hEab.2 _ ((hmemE' g).1 hg)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
