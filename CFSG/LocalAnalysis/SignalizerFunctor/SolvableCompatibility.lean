module

public import CFSG.LocalAnalysis.SignalizerFunctor.LocalCompleteness
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableNormalProducts

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

@[expose] def solvableSignalizerCompatible (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (target : Subgroup GroupType) : Prop :=
  signalizerCompatible prime rank actor values target ∧ Group.IsSolvable target

omit [Finite GroupType] in
theorem solvable_signalizer_compatible_of_le (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (larger smaller : Subgroup GroupType)
    (compatible : solvableSignalizerCompatible prime rank actor values larger)
    (contained : smaller ≤ larger)
    (normalized : actor ≤ Subgroup.normalizer (smaller : Set GroupType)) :
    solvableSignalizerCompatible prime rank actor values smaller := by
  let := compatible.2
  exact ⟨signalizer_compatible_of_le prime rank actor values compatible.1 contained normalized,
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective contained)⟩

theorem solvable_signalizer_sup_of_normalizing
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ rank ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected)))
    (normal other : Subgroup GroupType)
    (normal_compatible : solvableSignalizerCompatible prime rank actor values normal)
    (other_compatible : solvableSignalizerCompatible prime rank actor values other)
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType)) :
    solvableSignalizerCompatible prime rank actor values (normal ⊔ other) := by
  have other_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary large
    values coprime other other_compatible.1.1 other_compatible.1.2
  exact ⟨signalizer_sup_of_normalizing prime rank prime_prime actor elementary values normal other
    normal_compatible.1.1 other_compatible.1.1 normalizes other_coprime normal_compatible.1.2
    other_compatible.1.2,
    solvable_sup_of_normalizing normal other normalizes normal_compatible.2 other_compatible.2⟩

omit [Finite GroupType] in
theorem solvable_signalizer_value_compatible (prime rank : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    solvableSignalizerCompatible prime rank actor values (values selected) :=
  ⟨signalizer_value_compatible prime rank actor values conditions.normalized conditions.balanced member,
    conditions.solvable selected member⟩

theorem signalizer_normalizer_completion_control
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor target : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected)))
    (target_compatible : signalizerCompatible prime rank actor values target)
    (complete : signalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerRestriction values (Subgroup.normalizer (target : Set GroupType)) selected)) :
    let completion := ⨆ selected ∈ signalizerFunctorEk prime rank actor,
      signalizerRestriction values (Subgroup.normalizer (target : Set GroupType)) selected
    signalizerCompatible prime rank actor values completion ∧
      target ≤ completion ∧ (target.subgroupOf completion).Normal ∧
      (∀ other : Subgroup GroupType, signalizerCompatible prime rank actor values other →
        other ≤ Subgroup.normalizer (target : Set GroupType) → other ≤ completion) := by
  let ambient := Subgroup.normalizer (target : Set GroupType)
  let completion := ⨆ selected ∈ signalizerFunctorEk prime rank actor,
    signalizerRestriction values ambient selected
  have completion_contained : completion ≤ ambient :=
    iSup_le fun _ => iSup_le fun _ => inf_le_right
  have contains : ∀ other : Subgroup GroupType, signalizerCompatible prime rank actor values other →
      other ≤ ambient → other ≤ completion := by
    intro other compatible contained
    have restricted_compatible := (signalizer_restriction_compatible_of_le prime rank actor ambient
      other values contained).mpr compatible
    exact signalizer_maximality prime rank prime_prime actor elementary large
      (signalizerRestriction values ambient)
      (fun selected member => (coprime selected member).of_dvd_right
        (Subgroup.card_dvd_of_le inf_le_left)) other restricted_compatible.1 restricted_compatible.2
  have target_contained := contains target target_compatible Subgroup.le_normalizer
  exact ⟨complete, target_contained,
    (Subgroup.normal_subgroupOf_iff_le_normalizer target_contained).mpr completion_contained, contains⟩

theorem solvable_signalizer_restriction_completion
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor ambient : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (complete : solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected)) :
    solvableSignalizerCompatible prime rank actor (signalizerRestriction values ambient)
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, signalizerRestriction values ambient selected) := by
  let := complete.2
  have formula := signalizer_restriction_completion prime rank prime_prime actor ambient elementary
    large values conditions.coprime conditions.normalized ambient_normalized complete.1.2
  have contained : (⨆ selected ∈ signalizerFunctorEk prime rank actor,
      signalizerRestriction values ambient selected) ≤
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) := by
    rw [formula]
    exact inf_le_left
  exact ⟨signalizer_restriction_complete_of_compatible prime rank actor ambient values ambient_normalized
    conditions.normalized complete.1,
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective contained)⟩

end CFSG.SignalizerFunctor.Helpers
