module

public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalProduct

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

abbrev ambientConjugationAction (actor : Subgroup GroupType) :
    MulDistribMulAction actor GroupType :=
  MulDistribMulAction.compHom GroupType (MulAut.conj.comp actor.subtype)

theorem ambient_conjugation_fixed_eq_centralizer (actor : Subgroup GroupType) :
    let _action := ambientConjugationAction actor
    FixedPoints.subgroup actor GroupType = Subgroup.centralizer (actor : Set GroupType) := by
  let _action := ambientConjugationAction actor
  change FixedPoints.subgroup actor GroupType = Subgroup.centralizer (actor : Set GroupType)
  ext element
  constructor
  · intro fixed
    apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement member
    have equality := fixed (⟨actorElement, member⟩ : actor)
    change actorElement * element * actorElement⁻¹ = element at equality
    exact mul_inv_eq_iff_eq_mul.mp equality
  · intro central actorElement
    change actorElement.val * element * actorElement.val⁻¹ = element
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_iff.mp central actorElement.val actorElement.property)

theorem centralizer_sup_of_normalizing (prime : ℕ) (prime_prime : prime.Prime)
    (actor normal other : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (normalizes_normal : actor ≤ Subgroup.normalizer (normal : Set GroupType))
    (normalizes_other : actor ≤ Subgroup.normalizer (other : Set GroupType))
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType))
    (other_coprime : Nat.Coprime prime (Nat.card other)) :
    (normal ⊔ other) ⊓ Subgroup.centralizer (actor : Set GroupType) =
    (normal ⊓ Subgroup.centralizer (actor : Set GroupType)) ⊔
        (other ⊓ Subgroup.centralizer (actor : Set GroupType)) := by
  let _action := ambientConjugationAction actor
  let _baseAction : MulAction actor GroupType := _action.toMulAction
  have normal_invariant : ∀ actorElement : actor, ∀ element ∈ normal,
      actorElement • element ∈ normal := by
    intro actorElement element member
    exact Subgroup.le_normalizer_iff.mp normalizes_normal actorElement.val
      actorElement.property element member
  have other_invariant : ∀ actorElement : actor, ∀ element ∈ other,
      actorElement • element ∈ other := by
    intro actorElement element member
    exact Subgroup.le_normalizer_iff.mp normalizes_other actorElement.val
      actorElement.property element member
  rw [← ambient_conjugation_fixed_eq_centralizer actor]
  exact fixed_points_sup_of_normalizing prime prime_prime actor actor_pgroup GroupType
    normal other normalizes normal_invariant other_invariant other_coprime

theorem signalizer_sup_of_normalizing (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (normal other : Subgroup GroupType)
    (normalizes_normal : actor ≤ Subgroup.normalizer (normal : Set GroupType))
    (normalizes_other : actor ≤ Subgroup.normalizer (other : Set GroupType))
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType))
    (other_coprime : Nat.Coprime prime (Nat.card other))
    (normal_bounds : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      normal ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup)
    (other_bounds : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      other ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) :
    actor ≤ Subgroup.normalizer ((normal ⊔ other : Subgroup GroupType) : Set GroupType) ∧
    ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      (normal ⊔ other) ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup := by
  refine ⟨(le_inf normalizes_normal normalizes_other).trans
    (Subgroup.inf_normalizer_le_normalizer_sup normal other), ?_⟩
  intro subgroup member
  rw [centralizer_sup_of_normalizing prime prime_prime subgroup normal other
    (elementary_abelian_isPGroup prime subgroup (elementary_abelian_of_le prime elementary member.1))
    (member.1.trans normalizes_normal) (member.1.trans normalizes_other)
    normalizes other_coprime]
  exact sup_le (normal_bounds subgroup member) (other_bounds subgroup member)

end CFSG.SignalizerFunctor.Helpers
