module

public import CFSG.LocalAnalysis.SignalizerFunctor.OnePrimeCompleteness
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorization

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem signalizer_compatible_fixed_intersection (prime rank : ℕ) (actor target : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ≤ Subgroup.centralizer (selected : Set GroupType))
    (compatible : signalizerCompatible prime rank actor values target)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    target ⊓ Subgroup.centralizer (selected : Set GroupType) = target ⊓ values selected := by
  apply le_antisymm
  · exact le_inf inf_le_left (compatible.2 selected member)
  · exact inf_le_inf_left _ (central selected member)

theorem signalizer_common_conjugation_value (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (balanced : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values selected ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (element : signalizerCommonFixed prime rank actor values)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    conjugateSubgroup element.val (values selected) = values selected := by
  have contained : element.val ∈ values selected := by
    have member_fixed : element.val ∈ values selected ⊓ Subgroup.centralizer (actor : Set GroupType) := by
      rw [signalizer_value_common_fixed prime rank actor values balanced member]
      exact element.property
    exact member_fixed.1
  exact conjugate_subgroup_eq_of_mem element.val (values selected) contained

theorem signalizer_common_conjugation_index (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (element : signalizerCommonFixed prime rank actor values)
    (selected : Subgroup GroupType) (contained : selected ≤ actor) :
    conjugateSubgroup element.val selected = selected := by
  have commutes : ∀ actorElement ∈ selected, element.val * actorElement = actorElement * element.val := by
    intro actorElement member
    exact (Subgroup.mem_centralizer_iff.mp element.property.1 actorElement (contained member)).symm
  apply le_antisymm
  · rintro actorElement ⟨original, member, rfl⟩
    change element.val * original * element.val⁻¹ ∈ selected
    rw [commutes original member, mul_assoc, mul_inv_cancel, mul_one]
    exact member
  · intro actorElement member
    refine ⟨actorElement, member, ?_⟩
    change element.val * actorElement * element.val⁻¹ = actorElement
    rw [commutes actorElement member, mul_assoc, mul_inv_cancel, mul_one]

theorem signalizer_normalizer_completion_conjugate (prime rank : ℕ) (actor target : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (balanced : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values selected ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (element : signalizerCommonFixed prime rank actor values) :
    conjugateSubgroup element.val (signalizerNormalizerCompletion prime rank actor values target) =
      signalizerNormalizerCompletion prime rank actor values (conjugateSubgroup element.val target) := by
  change (⨆ selected ∈ signalizerFunctorEk prime rank actor,
    values selected ⊓ Subgroup.normalizer (target : Set GroupType)).map
      (MulAut.conj element.val).toMonoidHom = _
  rw [Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup]
  apply signalizer_completion_congr_values
  intro selected member
  rw [Subgroup.map_inf _ _ _ (MulAut.conj element.val).injective,
    Subgroup.map_equiv_normalizer_eq]
  change conjugateSubgroup element.val (values selected) ⊓
    Subgroup.normalizer (conjugateSubgroup element.val target : Set GroupType) =
    values selected ⊓ Subgroup.normalizer (conjugateSubgroup element.val target : Set GroupType)
  rw [signalizer_common_conjugation_value prime rank actor values balanced element selected member]

end CFSG.SignalizerFunctor.Helpers
