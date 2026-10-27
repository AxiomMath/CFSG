module

public import CFSG.Assembly.LowTwoRankDefs
import CFSG.LinearAlgebra.LinearGroups.Elementary

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup Matrix CFSG

universe u

theorem isSolvable_of_normal_pGroup_sup_cyclic {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {N T : Subgroup G} [N.Normal] (hN : IsPGroup p N) [IsCyclic T]
    (hNT : N ⊔ T = ⊤) : Group.IsSolvable G := by
  have : Group.IsNilpotent N := hN.isNilpotent
  have : Group.IsSolvable T := Group.isSolvable_of_comm (fun a b => mul_comm' a b)
  have hmap : T.map (QuotientGroup.mk' N) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hNT
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp T.subtype) := by
    intro y
    have hy : y ∈ T.map (QuotientGroup.mk' N) := hmap ▸ mem_top y
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨⟨t, ht⟩, rfl⟩
  have : Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_subgroup_quotient N

theorem isSolvable_of_le_sup_cyclic {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B U T : Subgroup G} (hUB : U ≤ B) (hTB : T ≤ B) (hUn : (U.subgroupOf B).Normal)
    (hU : IsPGroup p U) [IsCyclic T] (hsup : U ⊔ T = B) : Group.IsSolvable B := by
  have hN : IsPGroup p (U.subgroupOf B) :=
    hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUB).symm
  have : IsCyclic (T.subgroupOf B) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTB).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTB).symm.surjective
  refine isSolvable_of_normal_pGroup_sup_cyclic hN (T := T.subgroupOf B) ?_
  rw [← Subgroup.subgroupOf_sup hUB hTB, hsup, Subgroup.subgroupOf_self]

end CFSG.Quasithin.H13.QRC
