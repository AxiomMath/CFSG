module

public import CFSG.RankThree.PartOne.KE.TitsPlaneLocalCores
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne CFSG.Sporadic.Schreier.Tits
open CFSG.LocalAnalysis.ComponentInitial

theorem tits_normalized_component_local_core_product_odd_image :
    TitsNormalizedComponentLocalCoreProductOddImage := by
  intro G _ _ p hp hp3 E hE hEc t ht ht1 L hL ℓ f hmod hEL hSL
  obtain ⟨e⟩ := titsModelEquiv (L ⧸ Subgroup.center L) ℓ f hmod
  have hplane : PlaneLocalCoreOdd p (L ⧸ Subgroup.center L) :=
    PlaneLocalCoreOdd.of_mulEquiv hp e (planeLocalCoreOdd_tits p hp hp3)
  obtain ⟨hset, hWN, hodd, hres, -⟩ := component_local_core_odd_action_of_plane hp (by omega)
    hE hEc ht ht1 hL hEL hSL hplane
  refine ⟨componentLocalCoreOddImage_of_residual hL ⟨⟨hset, hWN, hodd⟩, hres⟩, ?_⟩
  intro hC
  have : Group.IsPerfect L := hL.1.1
  have hinj : Function.Injective
      ((Finkelstein1977.automizer L).comp (Subgroup.inclusion hEL)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 := (Finkelstein1977.automizer_eq_one_iff L (Subgroup.inclusion hEL x)).1 hx
    have h2 : (x : G) ∈ E ⊓ Subgroup.centralizer (L : Set G) := Subgroup.mem_inf.2 ⟨x.2, h1⟩
    rw [hC, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  exact tits_eq_five_of_injective_hom_mulAut e hp hp3 _ hinj hEc

end CFSG.RankThree.PartOne.KE
