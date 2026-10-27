module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleSubgroups

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def signalizerRestriction (values : Subgroup GroupType → Subgroup GroupType)
    (ambient : Subgroup GroupType) (selected : Subgroup GroupType) : Subgroup GroupType :=
  values selected ⊓ ambient

theorem signalizer_restriction_properties [Finite GroupType]
    (prime rank : ℕ) (actor ambient : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (central : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      values subgroup ≤ Subgroup.centralizer (subgroup : Set GroupType))
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other) :
    (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      signalizerRestriction values ambient subgroup ≤
        Subgroup.centralizer (subgroup : Set GroupType) ∧
      Nat.Coprime prime (Nat.card (signalizerRestriction values ambient subgroup)) ∧
      actor ≤ Subgroup.normalizer
        (signalizerRestriction values ambient subgroup : Set GroupType)) ∧
    (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        signalizerRestriction values ambient subgroup ⊓
          Subgroup.centralizer (other : Set GroupType) ≤
            signalizerRestriction values ambient other) := by
  refine ⟨?_, ?_⟩
  · intro subgroup member
    exact ⟨inf_le_left.trans (central subgroup member),
      (coprime subgroup member).of_dvd_right (Subgroup.card_dvd_of_le inf_le_left),
      normalizer_inf_of_le actor _ _ (normalized subgroup member) ambient_normalized⟩
  · intro subgroup member other other_member
    exact le_inf
      ((inf_le_inf_right _ inf_le_left).trans (balanced subgroup member other other_member))
      (inf_le_left.trans inf_le_right)

theorem signalizer_restriction_mcBride [Finite GroupType]
    (prime rank : ℕ) (actor ambient : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (hypothesis : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      signalizerMcBrideHypothesisB prime (values subgroup)) :
    ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      signalizerMcBrideHypothesisB prime (signalizerRestriction values ambient subgroup) := by
  intro subgroup member
  exact mcBrideHypothesisB_of_le prime inf_le_left (hypothesis subgroup member)

theorem signalizer_restriction_solvable
    (prime rank : ℕ) (actor ambient : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (solvable : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Group.IsSolvable (values subgroup)) :
    ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Group.IsSolvable (signalizerRestriction values ambient subgroup) := by
  intro subgroup member
  let := solvable subgroup member
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (show signalizerRestriction values ambient subgroup ≤
      values subgroup from inf_le_left))

theorem signalizer_restriction_compatible_of_le
    (prime rank : ℕ) (actor ambient target : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (contained : target ≤ ambient) :
    signalizerCompatible prime rank actor (signalizerRestriction values ambient) target ↔
      signalizerCompatible prime rank actor values target := by
  constructor
  · intro compatible
    exact ⟨compatible.1, fun subgroup member =>
      (compatible.2 subgroup member).trans inf_le_left⟩
  · intro compatible
    exact ⟨compatible.1, fun subgroup member =>
      le_inf (compatible.2 subgroup member) (inf_le_left.trans contained)⟩

theorem signalizer_restriction_compatible_iff [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor ambient target : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup))) :
    signalizerCompatible prime rank actor (signalizerRestriction values ambient) target ↔
      signalizerCompatible prime rank actor values target ∧ target ≤ ambient := by
  have restricted_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (signalizerRestriction values ambient subgroup)) := by
    intro subgroup member
    exact (coprime subgroup member).of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  constructor
  · intro compatible
    have contained : target ≤ ambient :=
      (signalizer_maximality prime rank prime_prime actor elementary large
        (signalizerRestriction values ambient) restricted_coprime target
        compatible.1 compatible.2).trans
          (iSup_le fun _ => iSup_le fun _ => inf_le_right)
    exact ⟨(signalizer_restriction_compatible_of_le prime rank actor ambient target values
      contained).mp compatible, contained⟩
  · rintro ⟨compatible, contained⟩
    exact (signalizer_restriction_compatible_of_le prime rank actor ambient target values
      contained).mpr compatible

theorem signalizer_restriction_completion [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor ambient : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (bounds : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ⊓
        Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) :
    (⨆ selected ∈ signalizerFunctorEk prime rank actor,
      signalizerRestriction values ambient selected) =
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ⊓ ambient := by
  let completion := ⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected
  have compatible : signalizerCompatible prime rank actor values (completion ⊓ ambient) :=
    signalizer_compatible_inf prime rank actor values completion ambient
      ⟨signalizer_completion_normalized prime rank actor values normalized, bounds⟩
      ambient_normalized
  have restricted_compatible :=
    (signalizer_restriction_compatible_of_le prime rank actor ambient
      (completion ⊓ ambient) values inf_le_right).mpr compatible
  apply le_antisymm
  · apply iSup_le
    intro selected
    apply iSup_le
    intro member
    exact le_inf
      (inf_le_left.trans (signalizer_value_le_completion prime rank actor values member))
      inf_le_right
  · exact signalizer_maximality prime rank prime_prime actor elementary large
      (signalizerRestriction values ambient)
      (fun subgroup member =>
        (coprime subgroup member).of_dvd_right (Subgroup.card_dvd_of_le inf_le_left))
      (completion ⊓ ambient) restricted_compatible.1 restricted_compatible.2

theorem signalizer_restriction_completion_bounds [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor ambient : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (bounds : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ⊓
        Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) :
    ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      (⨆ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerRestriction values ambient selected) ⊓
          Subgroup.centralizer (subgroup : Set GroupType) ≤
            signalizerRestriction values ambient subgroup := by
  rw [signalizer_restriction_completion prime rank prime_prime actor ambient elementary
    large values coprime normalized ambient_normalized bounds]
  intro subgroup member
  exact le_inf ((inf_le_inf_right _ inf_le_left).trans (bounds subgroup member))
    (inf_le_left.trans inf_le_right)

end CFSG.SignalizerFunctor.Helpers
