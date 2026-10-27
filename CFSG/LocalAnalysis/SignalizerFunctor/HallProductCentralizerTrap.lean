module

public import CFSG.LocalAnalysis.SignalizerFunctor.IncompleteHallProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalSylowPrimeExclusion

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_commutator_centralizer_disjoint (acting commutators target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (acting_le : acting ≤ factor) (commutators_le : commutators ≤ parent)
    (coprime : Nat.Coprime groupPrime (Nat.card commutators)) (nontrivial : commutators ≠ ⊥)
    (idempotent : ⁅commutators, acting⁆ = commutators)
    (normalized : acting ≤ Subgroup.normalizer (commutators : Set GroupType))
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (centralizes : commutators ≤ Subgroup.centralizer (target : Set GroupType)) : target ⊓ factor = ⊥ := by
  let : Fact groupPrime.Prime := ⟨datum.groupPrime_prime⟩
  by_contra intersection_nontrivial
  let intersection := target ⊓ factor
  have intersection_normalized := normalizer_inf_of_le actor target factor target_normalized datum.factor_compatible.1
  have trap := incomplete_abelian_hall_product_subgroup_normalizer_trap intersection datum abelian inf_le_right
    intersection_nontrivial intersection_normalized
  have commutators_normalizes : commutators ≤ Subgroup.normalizer (factor : Set GroupType) := by
    apply (le_inf commutators_le ?_).trans trap.2
    exact (centralizes.trans (Subgroup.centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have commutator_factor : ⁅commutators, acting⁆ ≤ factor := by
    apply (Subgroup.commutator_mono le_rfl acting_le).trans
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_normalizing factor commutators commutators_normalizes
  have factor_disjoint : commutators ⊓ factor = ⊥ := by
    obtain ⟨exponent, cardinality⟩ := datum.factor_pgroup.exists_card_eq
    have orders_coprime : Nat.Coprime (Nat.card commutators) (Nat.card factor) := by
      rw [cardinality]
      exact datum.groupPrime_prime.coprime_pow_of_not_dvd (datum.groupPrime_prime.coprime_iff_not_dvd.mp coprime)
    exact (Subgroup.disjoint_of_coprime_natCard orders_coprime).eq_bot
  have commutator_trivial : ⁅commutators, acting⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf (commutator_le_of_normalizing commutators acting normalized) commutator_factor).trans
      factor_disjoint.le
  exact nontrivial (idempotent.symm.trans commutator_trivial)

theorem incomplete_abelian_hall_product_commutator_centralizer_coprime (acting commutators target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (acting_le : acting ≤ factor) (acting_nontrivial : acting ≠ ⊥)
    (commutators_le : commutators ≤ parent) (coprime : Nat.Coprime groupPrime (Nat.card commutators))
    (nontrivial : commutators ≠ ⊥) (idempotent : ⁅commutators, acting⁆ = commutators)
    (normalized : acting ≤ Subgroup.normalizer (commutators : Set GroupType))
    (target_le : target ≤ parent) (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (acting_normalized : actor ≤ Subgroup.normalizer (acting : Set GroupType))
    (acting_normalizes_target : acting ≤ Subgroup.normalizer (target : Set GroupType))
    (centralizes : commutators ≤ Subgroup.centralizer (target : Set GroupType)) :
    Nat.Coprime groupPrime (Nat.card target) := by
  have disjoint := incomplete_abelian_hall_product_commutator_centralizer_disjoint acting commutators target datum
    abelian acting_le commutators_le coprime nontrivial idempotent normalized target_normalized centralizes
  let combined := target ⊔ acting
  have combined_le : combined ≤ parent := sup_le target_le (acting_le.trans datum.factor_le)
  have combined_normalized : actor ≤ Subgroup.normalizer (combined : Set GroupType) :=
    (le_inf target_normalized acting_normalized).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have combined_intersection_nontrivial : combined ⊓ factor ≠ ⊥ := by
    intro trivial
    apply acting_nontrivial
    apply le_bot_iff.mp
    exact (le_inf (le_sup_right : acting ≤ combined) acting_le).trans trivial.le
  obtain ⟨sylow, sylow_equal⟩ := incomplete_abelian_hall_product_sylow_intersection combined datum abelian combined_le
    combined_normalized combined_intersection_nontrivial
  let internal := target.subgroupOf combined
  let _normal : internal.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : target ≤ combined)).mpr
    (sup_le Subgroup.le_normalizer acting_normalizes_target)
  have internal_intersection : internal ⊓ (sylow : Subgroup combined) = ⊥ := by
    apply le_bot_iff.mp
    intro element member
    have factor_member : element.val ∈ factor := by
      rw [sylow_equal] at member
      exact member.2
    have target_factor : element.val ∈ target ⊓ factor := ⟨member.1, factor_member⟩
    rw [disjoint] at target_factor
    exact Subtype.ext target_factor
  have internal_coprime := normal_subgroup_coprime_of_sylow_inf_bot groupPrime datum.groupPrime_prime internal sylow
    internal_intersection
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : target ≤ combined)).toEquiv] at internal_coprime
  exact internal_coprime

end CFSG.SignalizerFunctor.Helpers
