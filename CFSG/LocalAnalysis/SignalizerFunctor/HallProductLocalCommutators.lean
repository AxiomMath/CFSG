module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductLocalCentralizers
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableLocalCommutators

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_local_commutator_le_core
    (fixedActor selected acting target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (fixedActor_le : fixedActor ≤ actor)
    (selected_member : selected ∈ signalizerFunctorEk prime rank actor) (selected_le : selected ≤ fixedActor)
    (acting_le : acting ≤ factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType))
    (target_le : target ≤ parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType))
    (normalized : acting ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime groupPrime (Nat.card target)) :
    let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    ⁅target, acting⁆ ≤ (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype := by
  let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let localCore := (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype
  change ⁅target, acting⁆ ≤ localCore
  let _solvable := incomplete_hall_product_local_fixed_solvable fixedActor selected datum selected_member selected_le
  obtain ⟨sylow, sylow_equal⟩ := incomplete_hall_product_local_fixed_sylow fixedActor datum fixedActor_le
  have sylow_factor : (sylow : Subgroup localFixed).map localFixed.subtype ≤ factor := sylow_equal.le.trans inf_le_left
  let := abelian
  have sylow_abelian : IsMulCommutative (sylow : Subgroup localFixed) := by
    apply Subgroup.le_centralizer_iff_isMulCommutative.mp
    intro element member
    apply Subgroup.mem_centralizer_iff.mpr
    intro other other_member
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.le_centralizer factor
      (sylow_factor (Subgroup.mem_map_of_mem localFixed.subtype member))) other.val
      (sylow_factor (Subgroup.mem_map_of_mem localFixed.subtype other_member))
  have acting_local : acting ≤ localFixed := acting_le.trans (inf_le_inf_right _ datum.factor_le)
  have acting_sylow : acting.subgroupOf localFixed ≤ (sylow : Subgroup localFixed) := by
    intro element member
    have mapped_member : element.val ∈ (sylow : Subgroup localFixed).map localFixed.subtype := by
      rw [sylow_equal]
      exact acting_le member
    have equality := Subgroup.comap_map_eq_self_of_injective localFixed.subtype_injective (sylow : Subgroup localFixed)
    rw [← equality]
    exact mapped_member
  have internal_normalized : acting.subgroupOf localFixed ≤
      Subgroup.normalizer (target.subgroupOf localFixed : Set localFixed) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro conjugator conjugator_member element element_member
    exact Subgroup.le_normalizer_iff.mp normalized conjugator.val conjugator_member element.val element_member
  have internal_coprime : Nat.Coprime groupPrime (Nat.card (target.subgroupOf localFixed)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe target_le).toEquiv]
    exact coprime
  have internal_le := solvable_abelian_sylow_complement_commutator_le_core groupPrime datum.groupPrime_prime
    sylow sylow_abelian (acting.subgroupOf localFixed) (target.subgroupOf localFixed) acting_sylow
    internal_normalized internal_coprime
  have mapped_le := Subgroup.map_mono (f := localFixed.subtype) internal_le
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le target_le,
    Subgroup.map_subgroupOf_eq_of_le acting_local] at mapped_le

end CFSG.SignalizerFunctor.Helpers
