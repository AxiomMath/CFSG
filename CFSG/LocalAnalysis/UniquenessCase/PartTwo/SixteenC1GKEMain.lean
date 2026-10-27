module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKEConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKEData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Kit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62

theorem s16c1c_e16Sing {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaE16Sing H := by
  intro E hEH hEab hcard
  let κe : (V₀ ≃ₗ[ZMod 2] V₀) ≃* MulAut W :=
    MulEquiv.ofBijective (s16c1G_kappa β)
      ⟨s16c1G_kappa_injective β, s16c1G44_kappa_surjective β⟩
  let E' : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := E.comap (s16c1G_kappa β)
  have hmemE' : ∀ g, g ∈ E' ↔ s16c1G_kappa β g ∈ E := fun g => Iff.rfl
  have hcardE' : Nat.card E' = Nat.card E := by
    have h0 : E' = E.comap κe.toMonoidHom := rfl
    have h1 : E' = E.map κe.symm.toMonoidHom := by
      rw [h0]
      exact Subgroup.comap_equiv_eq_map_symm κe E
    rw [h1]
    exact Subgroup.card_map_of_injective κe.symm.injective
  have hE'Ω : E' ≤ Ω₀ true := by
    intro g hg
    obtain ⟨g', hg', heq⟩ := (s16c1G_mem_H_iff hβ _).1 (hEH ((hmemE' g).1 hg))
    rw [s16c1G_kappa_injective β heq]
    exact hg'
  have hE'ab : ∀ g ∈ E', ∀ k ∈ E', g * k = k * g := by
    intro g hg k hk
    apply s16c1G_kappa_injective β
    rw [map_mul, map_mul]
    exact hEab.1 _ ((hmemE' g).1 hg) _ ((hmemE' k).1 hk)
  have hE'2 : ∀ g ∈ E', g ^ 2 = 1 := by
    intro g hg
    apply s16c1G_kappa_injective β
    rw [map_pow, map_one]
    exact hEab.2 _ ((hmemE' g).1 hg)
  have hp : IsPGroup 2 E' := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE'2 x x.2⟩
  obtain ⟨g₀, -, hconj⟩ := s16c1c_exists_conj_mem_T_omega hE'Ω hp
  set ψ : (V₀ ≃ₗ[ZMod 2] V₀) →* (V₀ ≃ₗ[ZMod 2] V₀) :=
    (MulAut.conj g₀⁻¹).toMonoidHom with hψdef
  have hψ : ∀ x, ψ x = g₀⁻¹ * x * g₀ := fun x => by simp [hψdef, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := (MulAut.conj g₀⁻¹).injective
  let P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := E'.map ψ
  have hcardP : Nat.card P = 16 := by
    have h1 : Nat.card P = Nat.card E' := Subgroup.card_map_of_injective hψinj
    rw [h1, hcardE', hcard]
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hE'ab a ha b hb]
  have hP2 : ∀ x ∈ P, x ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE'2 a ha, map_one]
  have hPT : ∀ x ∈ P, x ∈ s16c1c_T := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hψ]
    exact (Subgroup.mem_inf.1 (hconj a ha)).1
  have hPΩ : ∀ x ∈ P, x ∈ Ω₀ true := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hψ]
    exact (Subgroup.mem_inf.1 (hconj a ha)).2
  have hmemP : ∀ x, x ∈ E' ↔ g₀⁻¹ * x * g₀ ∈ P := by
    intro x
    constructor
    · intro hx
      rw [← hψ]
      exact Subgroup.mem_map_of_mem ψ hx
    · rintro ⟨a, ha, hax⟩
      rw [← hψ] at hax
      rwa [← hψinj hax]
  have hLinP : s16c1cE16Lin P := s16c1c_e16Lin_of_T hPab hP2 hPT hPΩ hcardP
  exact s16c1c_e16_transport β (E := E) (s16c1c_e16Lin_conj g₀ hmemP hLinP)

theorem omegaKitE16_holds : OmegaKitE16 := by
  intro W _ _ H h
  obtain ⟨β, hβ⟩ := natOmegaMinus_exists_model h
  exact s16c1c_e16Sing hβ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
