module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartOne.S11d.Facts5

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG

theorem isComponentOf_comap_of_injective {G H : Type} [Group G] [Group H] (ι : G →* H)
    (hι : Function.Injective ι) {N : Subgroup G} {E : Subgroup H}
    (hE : IsComponentOf (N.map ι) E) : IsComponentOf N (E.comap ι) := by
  have hEN : E ≤ N.map ι := hE.1
  have hEr : E ≤ ι.range := hEN.trans (Subgroup.map_le_range ι N)
  have hmap : (E.comap ι).map ι = E := Subgroup.map_comap_eq_self hEr
  have hsub : E.comap ι ≤ N := by
    intro g hg
    obtain ⟨g', hg', hgg'⟩ := hEN hg
    have : g' = g := hι hgg'
    rw [← this]
    exact hg'
  refine ⟨hsub, ?_, ?_⟩
  · have e : ↥(E.comap ι) ≃* ↥E :=
      (Subgroup.equivMapOfInjective (E.comap ι) ι hι).trans (MulEquiv.subgroupCongr hmap)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hE.2.1
  · let ψ : ↥N ≃* ↥(N.map ι) := Subgroup.equivMapOfInjective N ι hι
    have h : E.subgroupOf (N.map ι) = ((E.comap ι).subgroupOf N).map ψ.toMonoidHom := by
      ext g
      constructor
      · intro hg
        have hg' : (g : H) ∈ E := hg
        obtain ⟨y, hy, hyg⟩ := g.2
        refine ⟨⟨y, hy⟩, ?_, Subtype.ext hyg⟩
        show ι y ∈ E
        rw [hyg]
        exact hg'
      · rintro ⟨y, hy, rfl⟩
        exact hy
    have h2 := hE.2.2.map (f := ψ.symm.toMonoidHom) ψ.symm.surjective
    rw [h] at h2
    have h3 : (((E.comap ι).subgroupOf N).map ψ.toMonoidHom).map ψ.symm.toMonoidHom =
        (E.comap ι).subgroupOf N := by
      rw [Subgroup.map_map]
      have h4 : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id _ :=
        MonoidHom.ext fun x => ψ.symm_apply_apply x
      rw [h4, Subgroup.map_id]
    rwa [h3] at h2

end CFSG.RankThree.PartOne.FOC
