module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalCores

open Subgroup

variable {G : Type*} [Group G]

theorem not_isSolvable_of_isComponent {K : Subgroup G} (hK : IsComponent K) :
    ¬ Group.IsSolvable K := by
  have : Nontrivial K := isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect K := hK.1.1
  exact Group.IsPerfect.not_isSolvable K

theorem not_isComponent_of_le_solvable {K R : Subgroup G} (hK : IsComponent K) (hKR : K ≤ R)
    (hR : Group.IsSolvable R) : False :=
  not_isSolvable_of_isComponent hK
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKR))

theorem not_isComponent_of_normal_solvable [Finite G] {R : Subgroup G} (hRn : R.Normal)
    (hR : Group.IsSolvable R) (hC : Group.IsSolvable (centralizer (R : Set G)))
    (K : Subgroup G) : ¬ IsComponent K := by
  intro hK
  rcases component_normal_subgroup hK hRn with h | h
  · exact not_isComponent_of_le_solvable hK h hR
  · exact not_isComponent_of_le_solvable hK
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) hC

theorem not_isComponent_of_self_centralizing [Finite G] {R : Subgroup G} (hRn : R.Normal)
    (hR : Group.IsSolvable R) (hC : centralizer (R : Set G) ≤ R) (K : Subgroup G) :
    ¬ IsComponent K :=
  not_isComponent_of_normal_solvable hRn hR
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hC)) K

theorem not_isComponent_of_pGroup_self_centralizing [Finite G] {p : ℕ} [Fact p.Prime]
    {R : Subgroup G} (hRn : R.Normal) (hR : IsPGroup p R) (hC : centralizer (R : Set G) ≤ R)
    (K : Subgroup G) : ¬ IsComponent K := by
  have : Group.IsNilpotent R := hR.isNilpotent
  exact not_isComponent_of_self_centralizing hRn inferInstance hC K

theorem not_isComponent_le_of_self_centralizing [Finite G] {L R : Subgroup G} (hRL : R ≤ L)
    (hRn : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R) (hR : Group.IsSolvable R)
    (hC : ∀ l ∈ L, (∀ r ∈ R, l * r = r * l) → l ∈ R) {K : Subgroup G} (hK : IsComponent K)
    (hKL : K ≤ L) : False := by
  have hK' : IsComponent (K.subgroupOf L) := component_overgroup hK hKL
  have hn : (R.subgroupOf L).Normal :=
    ⟨fun r hr l => Subgroup.mem_subgroupOf.2 (hRn l l.2 r (Subgroup.mem_subgroupOf.1 hr))⟩
  have hs : Group.IsSolvable (R.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hRL).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRL).injective
  have hc : centralizer ((R.subgroupOf L : Subgroup L) : Set L) ≤ R.subgroupOf L := by
    intro l hl
    refine Subgroup.mem_subgroupOf.2 (hC l l.2 fun r hr => ?_)
    have h1 := Subgroup.mem_centralizer_iff.1 hl ⟨r, hRL hr⟩ (Subgroup.mem_subgroupOf.2 hr)
    exact (congrArg Subtype.val h1).symm
  exact not_isComponent_of_self_centralizing hn hs hc _ hK'

end CFSG.LocalCores
