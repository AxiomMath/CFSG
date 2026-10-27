module

public import CFSG.RankThree.GroupTheory.ThetaComponents
import CFSG.GroupTheory.SubnormalJoin

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

private theorem isSubnormal_subgroupOf_sSup {G : Type} [Group G] [Finite G] {C : Subgroup G}
    {𝒳 : Set (Subgroup G)} (h : ∀ L ∈ 𝒳, L ≤ C ∧ (L.subgroupOf C).IsSubnormal) :
    ((sSup 𝒳).subgroupOf C).IsSubnormal := by
  have hle : sSup 𝒳 ≤ C := sSup_le fun L hL => (h L hL).1
  set 𝒮 : Set (Subgroup C) := (fun L : Subgroup G => L.subgroupOf C) '' 𝒳 with h𝒮
  have h1 := (CFSG.GroupTheory.subnormal_subgroups_generated_join 𝒮
    (by rintro _ ⟨L, hL, rfl⟩; exact (h L hL).2)).1
  have h2 : Subgroup.closure (⋃ A ∈ 𝒮, (A : Set C)) = (sSup 𝒳).subgroupOf C := by
    rw [Set.biUnion_eq_iUnion, ← Subgroup.iSup_eq_closure, ← sSup_eq_iSup']
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hle, h𝒮, sSup_image, sSup_eq_iSup]
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun L => iSup_congr fun hL => Subgroup.map_subgroupOf_eq_of_le (h L hL).1
  rwa [h2] at h1

private theorem inSubgroup_theta_map_subtype {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (K : Subgroup C) :
    inSubgroup (aschbacherSolvableCore 3) (K.map C.subtype) =
      (inSubgroup (aschbacherSolvableCore 3) K).map C.subtype := by
  rw [inSubgroup, inSubgroup, Subgroup.map_map,
    ← aschbacherSolvableCore_map_mulEquiv Nat.prime_three
      (K.equivMapOfInjective C.subtype C.subtype_injective), Subgroup.map_map]
  rfl

theorem theta_sSup_le {G : Type} [Group G] [Finite G] {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) :
    inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  have hmem : ∀ L ∈ 𝒳, L ≤ C ∧ (L.subgroupOf C).IsSubnormal := by
    intro L hL
    obtain ⟨L', hL', rfl⟩ := h𝒳 hL
    refine ⟨Subgroup.map_subtype_le L', ?_⟩
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact hL'.2.1
  have hle : sSup 𝒳 ≤ C := sSup_le fun L hL => (hmem L hL).1
  have h1 := solvable_prime_complement_core_subnormal_intersection Nat.prime_three
    (isSubnormal_subgroupOf_sSup hmem)
  rw [← Subgroup.map_subgroupOf_eq_of_le hle, inSubgroup_theta_map_subtype, h1]
  exact Subgroup.map_mono inf_le_right

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
