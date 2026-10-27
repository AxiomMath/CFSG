module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

attribute [local instance] LocalCores.layer_characteristic

theorem le_of_isPerfect_of_isSolvable_quotient {H : Type*} [Group H] {N L : Subgroup H}
    [N.Normal] (hsol : Group.IsSolvable (H ⧸ N)) (hL : Group.IsPerfect L) : L ≤ N := by
  set π := QuotientGroup.mk' N
  have hperf : Group.IsPerfect (L.map π) := by
    have := hL
    exact Group.IsPerfect.ofSurjective (π.subgroupMap_surjective L)
  have hbot : L.map π = ⊥ := by
    by_contra hne
    have : Nontrivial (L.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hsol' : Group.IsSolvable (L.map π) :=
      Group.isSolvable_of_isSolvable_injective (L.map π).subtype_injective
    exact Group.IsPerfect.not_isSolvable (L.map π) hsol'
  rw [← QuotientGroup.ker_mk' N]
  exact (Subgroup.map_eq_bot_iff L).mp hbot

end CFSG.RankThree.GroupTheory
