module

public import CFSG.Quasithin.EmptyFaithful.A38c5Hom

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace CFSG.Quasithin.A38c5

section Q

variable {A B₁ B₂ : Type} [Group A] [Group B₁] [Group B₂]

theorem exists_injective_factor (f₁ : A →* B₁) (f₂ : A →* B₂) (hker : f₁.ker = f₂.ker) :
    ∃ g : f₁.range →* B₂, Function.Injective g ∧ ∀ a, g (f₁.rangeRestrict a) = f₂ a := by
  have hsurj : Function.Surjective f₁.rangeRestrict := f₁.rangeRestrict_surjective
  have hle : f₁.rangeRestrict.ker ≤ f₂.ker := by
    rw [MonoidHom.ker_rangeRestrict, hker]
  let g : f₁.range →* B₂ := (MonoidHom.liftOfSurjective f₁.rangeRestrict hsurj) ⟨f₂, hle⟩
  have hg : ∀ a, g (f₁.rangeRestrict a) = f₂ a := fun a => by
    simp [g]
  refine ⟨g, ?_, hg⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨a, rfl⟩ := hsurj y
  rw [hg] at hy
  have : a ∈ f₂.ker := hy
  rw [← hker, MonoidHom.mem_ker] at this
  ext
  simpa using this

theorem map_eq_map_rangeRestrict_map (f₁ : A →* B₁) (L : Subgroup A) :
    L.map f₁ = (L.map f₁.rangeRestrict).map f₁.range.subtype := by
  rw [Subgroup.map_map]
  rfl

theorem map_eq_map_rangeRestrict_map' (f₁ : A →* B₁) (f₂ : A →* B₂) (g : f₁.range →* B₂)
    (hgf : ∀ a, g (f₁.rangeRestrict a) = f₂ a) (L : Subgroup A) :
    L.map f₂ = (L.map f₁.rangeRestrict).map g := by
  rw [Subgroup.map_map]
  congr 1
  ext a
  exact (hgf a).symm

theorem isMaxParabolic2_map_iff_of_ker_eq (f₁ : A →* B₁) (f₂ : A →* B₂) (hker : f₁.ker = f₂.ker)
    (L P : Subgroup A) :
    IsMaxParabolic2 (L.map f₁) (P.map f₁) ↔ IsMaxParabolic2 (L.map f₂) (P.map f₂) := by
  obtain ⟨g, hg, hgf⟩ := exists_injective_factor f₁ f₂ hker
  rw [map_eq_map_rangeRestrict_map f₁ L, map_eq_map_rangeRestrict_map f₁ P,
    map_eq_map_rangeRestrict_map' f₁ f₂ g hgf L, map_eq_map_rangeRestrict_map' f₁ f₂ g hgf P,
    isMaxParabolic2_map_iff _ f₁.range.subtype_injective, isMaxParabolic2_map_iff _ hg]

theorem nonempty_mulEquiv_map_of_ker_eq (f₁ : A →* B₁) (f₂ : A →* B₂) (hker : f₁.ker = f₂.ker)
    (L : Subgroup A) : Nonempty (↥(L.map f₁) ≃* ↥(L.map f₂)) := by
  obtain ⟨g, hg, hgf⟩ := exists_injective_factor f₁ f₂ hker
  let L' := L.map f₁.rangeRestrict
  have e1 : ↥(L.map f₁) ≃* ↥L' :=
    (MulEquiv.subgroupCongr (map_eq_map_rangeRestrict_map f₁ L)).trans
      (L'.equivMapOfInjective f₁.range.subtype f₁.range.subtype_injective).symm
  have e2 : ↥L' ≃* ↥(L.map f₂) :=
    (L'.equivMapOfInjective g hg).trans
      (MulEquiv.subgroupCongr (map_eq_map_rangeRestrict_map' f₁ f₂ g hgf L).symm)
  exact ⟨e1.trans e2⟩

end Q
end CFSG.Quasithin.A38c5
