module

public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.LocalCores.Components
public import Mathlib.Algebra.Group.Commutator
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

theorem map_subgroupOf_sSup {X B : Type*} [Group X] [Group B] {H : Subgroup X} (f : ↥H →* B)
    {𝒞 : Set (Subgroup X)} (h𝒞 : ∀ S ∈ 𝒞, S ≤ H) :
    ((sSup 𝒞).subgroupOf H).map f = sSup ((fun S => (S.subgroupOf H).map f) '' 𝒞) := by
  have hA : (sSup 𝒞).subgroupOf H = sSup ((fun S => S.subgroupOf H) '' 𝒞) := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (sSup_le h𝒞),
      (Subgroup.gc_map_comap H.subtype).l_sSup_eq_sSup_image, Set.image_image]
    congr 1
    ext S
    constructor
    · intro hS
      exact ⟨S, hS, Subgroup.map_subgroupOf_eq_of_le (h𝒞 S hS)⟩
    · rintro ⟨T, hT, rfl⟩
      change (T.subgroupOf H).map H.subtype ∈ 𝒞
      rwa [Subgroup.map_subgroupOf_eq_of_le (h𝒞 T hT)]
  rw [hA, (Subgroup.gc_map_comap f).l_sSup_eq_sSup_image, Set.image_image]

end CFSG.StandardType
