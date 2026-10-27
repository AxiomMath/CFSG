module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem noncentralSylow_kernel_normalizer_growth
    (p : ℕ) (hp : p.Prime) (T W : Subgroup G)
    (hT : IsPGroup p T) (hWT : W < T)
    {Q : Type*} [Group Q] (f : G →* Q) (himages : W.map f = T.map f) :
    ∃ x : G, x ∈ T ∧ x ∈ f.ker ∧
      x ∈ Subgroup.normalizer (W : Set G) ∧ x ∉ W := by
  have hgrowth := pSubgroup_lt_normalizer_intersection p hp W T hT hWT
  obtain ⟨y, hy, hyW⟩ := IsConcreteLE.exists_of_lt hgrowth
  have hyimage : f y ∈ W.map f := by
    rw [himages]
    exact Subgroup.mem_map_of_mem f hy.1
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hyimage
  let x := y * w⁻¹
  have hxT : x ∈ T := T.mul_mem hy.1 (T.inv_mem (hWT.le hw))
  have hxker : x ∈ f.ker := by
    apply MonoidHom.mem_ker.mpr
    change f (y * w⁻¹) = 1
    rw [map_mul, map_inv, hwy, mul_inv_cancel]
  have hxN : x ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normalizer (W : Set G)).mul_mem hy.2
      ((Subgroup.normalizer (W : Set G)).inv_mem (Subgroup.le_normalizer hw))
  refine ⟨x, hxT, hxker, hxN, ?_⟩
  intro hxW
  apply hyW
  have hmul := W.mul_mem hxW hw
  simpa only [x, mul_assoc, inv_mul_cancel, mul_one] using hmul

omit [Finite G] in
theorem noncentralSylow_containing_pgroup_intersection
    (p : ℕ) (E : Subgroup G) (A : Sylow p E)
    (T : Subgroup G) (hT : IsPGroup p T)
    (hAT : (A : Subgroup E).map E.subtype ≤ T) :
    T ⊓ E = (A : Subgroup E).map E.subtype := by
  have hAp : (A : Subgroup E) ≤ T.subgroupOf E := by
    intro a ha
    exact hAT (Subgroup.mem_map_of_mem E.subtype ha)
  have heq := A.is_maximal' hT.comap_subtype hAp
  have hmap := congrArg (Subgroup.map E.subtype) heq
  change (T.subgroupOf E).map E.subtype = (A : Subgroup E).map E.subtype at hmap
  rw [Subgroup.subgroupOf_map_subtype] at hmap
  exact hmap

end CFSG.ShultStronglyClosedTI
