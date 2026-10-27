module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedPointLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantActions
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType]

@[expose] def actionCommutator : Subgroup GroupType :=
  Subgroup.closure {difference | ∃ actorElement : ActorType, ∃ element : GroupType,
    element⁻¹ * (actorElement • element) = difference}

theorem action_commutator_generator (actorElement : ActorType) (element : GroupType) :
    element⁻¹ * (actorElement • element) ∈ actionCommutator (ActorType := ActorType) :=
  Subgroup.subset_closure ⟨actorElement, element, rfl⟩

theorem action_commutator_normal :
    (actionCommutator (ActorType := ActorType) (GroupType := GroupType)).Normal := by
  have conjugation_le : ∀ conjugator : GroupType,
      (actionCommutator (ActorType := ActorType)).map (MulAut.conj conjugator).toMonoidHom ≤
        actionCommutator (ActorType := ActorType) := by
    intro conjugator
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨actorElement, element, rfl⟩
    change conjugator * (element⁻¹ * (actorElement • element)) * conjugator⁻¹ ∈ actionCommutator (ActorType := ActorType)
    have first := action_commutator_generator actorElement (element * conjugator⁻¹)
    have second := action_commutator_generator actorElement conjugator⁻¹
    have product := Subgroup.mul_mem (actionCommutator (ActorType := ActorType)) first
      (Subgroup.inv_mem _ second)
    have equal : (element * conjugator⁻¹)⁻¹ * (actorElement • (element * conjugator⁻¹)) *
        (conjugator⁻¹⁻¹ * (actorElement • conjugator⁻¹))⁻¹ =
        conjugator * (element⁻¹ * (actorElement • element)) * conjugator⁻¹ := by
      rw [MulDistribMulAction.smul_mul]
      group
    rwa [equal] at product
  constructor
  intro element member conjugator
  exact conjugation_le conjugator (Subgroup.mem_map_of_mem (MulAut.conj conjugator).toMonoidHom member)

theorem action_commutator_invariant :
    ∀ actorElement : ActorType, ∀ element ∈ actionCommutator (ActorType := ActorType) (GroupType := GroupType),
      actorElement • element ∈ actionCommutator (ActorType := ActorType) := by
  intro actorElement element member
  have map_le : (actionCommutator (ActorType := ActorType)).map
      (MulDistribMulAction.toMonoidHom GroupType actorElement) ≤ actionCommutator (ActorType := ActorType) := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨otherActor, original, rfl⟩
    change actorElement • (original⁻¹ * (otherActor • original)) ∈ actionCommutator (ActorType := ActorType)
    have generated := action_commutator_generator (actorElement * otherActor * actorElement⁻¹)
      (actorElement • original)
    have equal : (actorElement • original)⁻¹ *
        ((actorElement * otherActor * actorElement⁻¹) • (actorElement • original)) =
        actorElement • (original⁻¹ * (otherActor • original)) := by
      simp only [mul_smul, inv_smul_smul, MulDistribMulAction.smul_mul, smul_inv']
    rwa [equal] at generated
  exact map_le (Subgroup.mem_map_of_mem _ member)

theorem action_commutator_quotient_trivial :
    let commutators := actionCommutator (ActorType := ActorType) (GroupType := GroupType)
    let _normal := action_commutator_normal (ActorType := ActorType) (GroupType := GroupType)
    let _action := invariantQuotientAction commutators action_commutator_invariant
    ∀ actorElement : ActorType, ∀ element : GroupType ⧸ commutators, actorElement • element = element := by
  let commutators := actionCommutator (ActorType := ActorType) (GroupType := GroupType)
  let _normal := action_commutator_normal (ActorType := ActorType) (GroupType := GroupType)
  let _action := invariantQuotientAction commutators action_commutator_invariant
  change ∀ actorElement : ActorType, ∀ element : GroupType ⧸ commutators, actorElement • element = element
  intro actorElement element
  induction element using QuotientGroup.induction_on with
  | H element =>
    change QuotientGroup.mk' commutators (actorElement • element) = QuotientGroup.mk' commutators element
    have generator_one : QuotientGroup.mk' commutators (element⁻¹ * (actorElement • element)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (action_commutator_generator actorElement element)
    rw [map_mul, map_inv, inv_mul_eq_one] at generator_one
    exact generator_one.symm

theorem coprime_action_commutator_factorization [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) :
    actionCommutator (ActorType := ActorType) (GroupType := GroupType) ⊔
      FixedPoints.subgroup ActorType GroupType = ⊤ := by
  let commutators := actionCommutator (ActorType := ActorType) (GroupType := GroupType)
  let _normal := action_commutator_normal (ActorType := ActorType) (GroupType := GroupType)
  let _action := invariantQuotientAction commutators action_commutator_invariant
  let projection := QuotientGroup.mk' commutators
  have fixed_top : FixedPoints.subgroup ActorType (GroupType ⧸ commutators) = ⊤ := by
    apply top_unique
    intro element _ actorElement
    exact action_commutator_quotient_trivial actorElement element
  have kernel_coprime : Nat.Coprime prime (Nat.card projection.ker) := by
    rw [QuotientGroup.ker_mk']
    exact coprime.of_dvd_right commutators.card_subgroup_dvd_card
  have fixed_image := fixed_subgroup_map prime prime_prime actor_pgroup projection
    (QuotientGroup.mk'_surjective commutators) (invariant_quotient_equivariant commutators action_commutator_invariant)
    kernel_coprime
  rw [fixed_top] at fixed_image
  have preimage := congrArg (Subgroup.comap projection) fixed_image
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at preimage
  exact (sup_comm _ _).trans preimage

end CFSG.SignalizerFunctor.Helpers
