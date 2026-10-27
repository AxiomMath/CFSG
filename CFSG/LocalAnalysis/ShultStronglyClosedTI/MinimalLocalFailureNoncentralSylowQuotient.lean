module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowBridge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowExtension

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] [Finite G]

theorem noncentralSylow_surjective_subgroup_sylow_image
    (p : ℕ) (hp : p.Prime) (B E : Subgroup G) (hEB : E ≤ B)
    {Q : Type*} [Group Q] (f : B →* Q)
    (hsurj : Function.Surjective (f.domRestrict (E.subgroupOf B)))
    (A : Sylow p E) :
    ∃ R : Sylow p Q, (R : Subgroup Q) =
      (((A : Subgroup E).map E.subtype).subgroupOf B).map f := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨A₀, hA₀⟩ := sylow_subgroupOf_restriction_ambient_image p hp E B hEB A
  let EB := E.subgroupOf B
  let R := A₀.mapSurjective (f := f.domRestrict EB) hsurj
  have hsubtype : (A₀ : Subgroup EB).map EB.subtype =
      (((A : Subgroup E).map E.subtype).subgroupOf B) := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.map_subtype_le _).trans hEB)]
    exact hA₀
  refine ⟨R, ?_⟩
  rw [Sylow.coe_mapSurjective]
  change (A₀ : Subgroup EB).map (f.comp EB.subtype) = _
  rw [← Subgroup.map_map, hsubtype]

theorem noncentralSylow_containing_pgroup_image_eq
    (p : ℕ) (hp : p.Prime) (B E : Subgroup G) (hEB : E ≤ B)
    {Q : Type*} [Group Q] (f : B →* Q)
    (hsurj : Function.Surjective (f.domRestrict (E.subgroupOf B)))
    (A : Sylow p E) (T : Subgroup G) (hT : IsPGroup p T)
    (hAT : (A : Subgroup E).map E.subtype ≤ T) :
    (((A : Subgroup E).map E.subtype).subgroupOf B).map f = (T.subgroupOf B).map f := by
  obtain ⟨R, hR⟩ := noncentralSylow_surjective_subgroup_sylow_image p hp B E hEB f hsurj A
  have hTR : IsPGroup p ((T.subgroupOf B).map f) :=
    hT.comap_subtype.map f
  have hRT : (R : Subgroup Q) ≤ (T.subgroupOf B).map f := by
    rw [hR]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono B hAT)
  exact hR.symm.trans (R.is_maximal' hTR hRT).symm

end CFSG.ShultStronglyClosedTI
