module

public import TauCeti.Algebra.Group.Subgroup.Map

public section

namespace Subgroup

theorem closure_subgroupOf {G : Type*} [Group G] {H : Subgroup G} {S : Set G} (hSH : S ⊆ H) :
    (Subgroup.closure S).subgroupOf H = Subgroup.closure (H.subtype ⁻¹' S) :=
  (Subgroup.closure_coe_preimage_of_subset hSH).symm

end Subgroup

end
