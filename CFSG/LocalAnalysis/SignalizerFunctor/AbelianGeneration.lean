module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedPointLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.IrreducibleAction
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantActions
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem abelian_cyclic_quotient_generation
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [CommGroup GroupType] [Finite GroupType]
    [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType)) :
    (⨆ (actorSubgroup : Subgroup ActorType) (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
      FixedPoints.subgroup actorSubgroup GroupType) = ⊤ := by
  classical
  suffices general_result : ∀ order : ℕ,
      ∀ (TargetType : Type groupUniverse) [CommGroup TargetType] [Finite TargetType]
        [MulDistribMulAction ActorType TargetType],
        Nat.card TargetType = order → Nat.Coprime prime (Nat.card TargetType) →
          (⨆ (actorSubgroup : Subgroup ActorType)
              (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
            FixedPoints.subgroup actorSubgroup TargetType) = ⊤ by
    exact general_result (Nat.card GroupType) GroupType rfl coprime
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro TargetType _ _ _ target_card target_coprime
    let generated : Subgroup TargetType :=
      ⨆ (actorSubgroup : Subgroup ActorType)
        (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
          FixedPoints.subgroup actorSubgroup TargetType
    change generated = ⊤
    rcases subsingleton_or_nontrivial TargetType with trivial | nontrivial
    · let := trivial
      apply top_unique
      intro element _
      have element_one : element = 1 := Subsingleton.elim _ _
      rw [element_one]
      exact generated.one_mem
    · let := nontrivial
      by_cases reducible : ∃ subgroup : Subgroup TargetType,
          subgroup ≠ ⊥ ∧ subgroup ≠ ⊤ ∧
            ∀ actorElement : ActorType, ∀ element ∈ subgroup,
              actorElement • element ∈ subgroup
      · obtain ⟨subgroup, subgroup_nontrivial, subgroup_proper, invariant⟩ := reducible
        let _subgroupAction := invariantSubgroupAction subgroup invariant
        let _quotientAction := invariantQuotientAction subgroup invariant
        have subgroup_coprime : Nat.Coprime prime (Nat.card subgroup) :=
          target_coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card subgroup)
        have quotient_coprime : Nat.Coprime prime (Nat.card (TargetType ⧸ subgroup)) :=
          target_coprime.of_dvd_right (Subgroup.card_quotient_dvd_card subgroup)
        have subgroup_smaller : Nat.card subgroup < order := by
          rw [← target_card]
          apply lt_of_le_of_ne subgroup.card_le_card_group
          intro equal_card
          exact subgroup_proper (subgroup.card_eq_iff_eq_top.mp equal_card)
        have quotient_smaller : Nat.card (TargetType ⧸ subgroup) < order := by
          rw [← target_card, subgroup.card_eq_card_quotient_mul_card_subgroup]
          have subgroup_large : 1 < Nat.card subgroup := by
            have positive : 0 < Nat.card subgroup := Nat.card_pos
            have not_one : Nat.card subgroup ≠ 1 := by
              intro equal_one
              exact subgroup_nontrivial (Subgroup.card_eq_one.mp equal_one)
            omega
          have quotient_positive : 0 < Nat.card (TargetType ⧸ subgroup) := Nat.card_pos
          nlinarith
        have subgroup_generated := induction_hypothesis (Nat.card subgroup)
          subgroup_smaller subgroup rfl subgroup_coprime
        have quotient_generated := induction_hypothesis (Nat.card (TargetType ⧸ subgroup))
          quotient_smaller (TargetType ⧸ subgroup) rfl quotient_coprime
        have subgroup_le : subgroup ≤ generated := by
          rw [← subgroup.subtype_range, MonoidHom.range_eq_map, ← subgroup_generated]
          rw [Subgroup.map_iSup]
          apply iSup_le
          intro actorSubgroup
          rw [Subgroup.map_iSup]
          apply iSup_le
          intro cyclic
          exact (invariant_subgroup_fixed_points_le subgroup invariant actorSubgroup).trans
            (le_iSup_of_le actorSubgroup (le_iSup_of_le cyclic le_rfl))
        let projection := QuotientGroup.mk' subgroup
        have kernel_coprime : Nat.Coprime prime (Nat.card projection.ker) := by
          simpa only [projection, QuotientGroup.ker_mk'] using subgroup_coprime
        have projected_whole : generated.map projection = ⊤ := by
          apply top_unique
          rw [← quotient_generated]
          apply iSup_le
          intro actorSubgroup
          apply iSup_le
          intro cyclic
          have equivariant : ∀ actorElement : actorSubgroup, ∀ element : TargetType,
              projection (actorElement • element) = actorElement • projection element := by
            intro actorElement element
            exact invariant_quotient_equivariant subgroup invariant actorElement.val element
          rw [← fixed_subgroup_map prime prime_prime (actor_pgroup.to_subgroup actorSubgroup)
            projection (QuotientGroup.mk'_surjective subgroup) equivariant kernel_coprime]
          exact Subgroup.map_mono
            (le_iSup_of_le actorSubgroup (le_iSup_of_le cyclic le_rfl))
        have kernel_le : projection.ker ≤ generated := by
          simpa only [projection, QuotientGroup.ker_mk'] using subgroup_le
        apply top_unique
        intro element _
        have image_member : projection element ∈ generated.map projection := by
          rw [projected_whole]
          trivial
        obtain ⟨representative, representative_member, same_image⟩ := image_member
        have difference_kernel : element * representative⁻¹ ∈ projection.ker := by
          change projection (element * representative⁻¹) = 1
          rw [map_mul, map_inv, same_image, mul_inv_cancel]
        have product_member := generated.mul_mem (kernel_le difference_kernel)
          representative_member
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using product_member
      · have irreducible : ∀ subgroup : Subgroup TargetType,
            (∀ actorElement : ActorType, ∀ element ∈ subgroup,
              actorElement • element ∈ subgroup) →
            subgroup = ⊥ ∨ subgroup = ⊤ := by
          intro subgroup invariant
          by_cases trivial : subgroup = ⊥
          · exact Or.inl trivial
          · right
            by_contra proper
            exact reducible ⟨subgroup, trivial, proper, invariant⟩
        obtain ⟨kernel, cyclic, fixed_whole⟩ :=
          cyclic_quotient_fixing_irreducible_abelian_group ActorType TargetType irreducible
        apply top_unique
        rw [← fixed_whole]
        exact le_iSup_of_le kernel (le_iSup_of_le cyclic le_rfl)

end CFSG.SignalizerFunctor.Helpers
