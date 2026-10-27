module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Mapping the Fitting subgroup into a homomorphism range

The image of a finite group's Fitting subgroup is a normal nilpotent
subgroup of the homomorphism range, hence lies in that range's Fitting
subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

/-- The Fitting subgroup maps into the Fitting subgroup of the homomorphism
range.  Restricting the codomain to the range makes normality available
without assuming that the original homomorphism is surjective. -/
public theorem fittingSubgroup_map_rangeRestrict_le
    {G : Type u} {H : Type v} [Group G] [Finite G] [Group H]
    (f : G →* H) :
    (fittingSubgroup G).map f.rangeRestrict ≤ fittingSubgroup f.range := by
  letI : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let N : Subgroup f.range := (fittingSubgroup G).map f.rangeRestrict
  have hNnormal : N.Normal := by
    dsimp [N]
    exact (fittingSubgroup_normal (G := G)).map f.rangeRestrict
      f.rangeRestrict_surjective
  have hNnil : Group.IsNilpotent N := by
    let g : fittingSubgroup G →* N :=
      (f.rangeRestrict.comp (fittingSubgroup G).subtype).codRestrict N
        (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    have hg : Function.Surjective g := by
      intro y
      rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
    exact Group.nilpotent_of_surjective g hg
  change N ≤ fittingSubgroup f.range
  exact le_sSup ⟨hNnormal, hNnil⟩

end CFSG.GorensteinWalter
