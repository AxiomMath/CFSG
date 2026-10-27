module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.Open.SignalizerFunctorTheoremMilestoneDefs

public section

open CFSG.Open

universe groupUniverse indexUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem normalizer_iSup_of_le {Index : Sort indexUniverse}
    (actor : Subgroup GroupType) (family : Index → Subgroup GroupType)
    (invariant : ∀ index, actor ≤ Subgroup.normalizer (family index : Set GroupType)) :
    actor ≤ Subgroup.normalizer ((⨆ index, family index : Subgroup GroupType) : Set GroupType) :=
  (le_iInf invariant).trans (Subgroup.iInf_normalizer_le_normalizer_iSup family)

theorem normalizer_biSup_of_le {Index : Type indexUniverse}
    (actor : Subgroup GroupType) (indices : Set Index)
    (family : Index → Subgroup GroupType)
    (invariant : ∀ index ∈ indices,
      actor ≤ Subgroup.normalizer (family index : Set GroupType)) :
    actor ≤ Subgroup.normalizer
      ((⨆ index ∈ indices, family index : Subgroup GroupType) : Set GroupType) := by
  apply normalizer_iSup_of_le
  intro index
  apply normalizer_iSup_of_le
  intro member
  exact invariant index member

theorem signalizer_value_le_completion (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    {subgroup : Subgroup GroupType} (member : subgroup ∈ signalizerFunctorEk prime rank actor) :
    values subgroup ≤ ⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected :=
  le_iSup_of_le subgroup (le_iSup_of_le member le_rfl)

theorem signalizer_completion_normalized (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (invariant : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType)) :
    actor ≤ Subgroup.normalizer
      ((⨆ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup :
        Subgroup GroupType) : Set GroupType) :=
  normalizer_biSup_of_le actor (signalizerFunctorEk prime rank actor) values invariant

theorem signalizer_value_le_completion_centralizer (prime rank : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      values subgroup ≤ Subgroup.centralizer (subgroup : Set GroupType))
    {subgroup : Subgroup GroupType} (member : subgroup ∈ signalizerFunctorEk prime rank actor) :
    values subgroup ≤
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ⊓
        Subgroup.centralizer (subgroup : Set GroupType) :=
  le_inf (signalizer_value_le_completion prime rank actor values member)
    (central subgroup member)

theorem mcBrideHypothesisB_of_le [Finite GroupType] (prime : ℕ)
    {larger smaller : Subgroup GroupType} (contained : smaller ≤ larger)
    (hypothesis : signalizerMcBrideHypothesisB prime larger) :
    signalizerMcBrideHypothesisB prime smaller := by
  refine ⟨hypothesis.1,
    hypothesis.2.1.of_dvd_right (Subgroup.card_dvd_of_le contained), ?_⟩
  intro numerator denominator numerator_le denominator_le normal simple nonabelian
  exact hypothesis.2.2 numerator denominator (numerator_le.trans contained) denominator_le
    simple nonabelian

theorem solvable_simple_section_commutative [Finite GroupType]
    {larger numerator denominator : Subgroup GroupType}
    [Group.IsSolvable larger] (contained : numerator ≤ larger)
    [(denominator.subgroupOf numerator).Normal]
    [IsSimpleGroup (numerator ⧸ denominator.subgroupOf numerator)] :
    ∀ first second : numerator ⧸ denominator.subgroupOf numerator,
      first * second = second * first := by
  let : Group.IsSolvable numerator :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion contained) (Subgroup.inclusion_injective contained)
  exact IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance

theorem mcBrideHypothesisB_of_solvable [Finite GroupType] (prime : ℕ)
    (prime_prime : prime.Prime) (subgroup : Subgroup GroupType)
    (coprime : Nat.Coprime prime (Nat.card subgroup)) [Group.IsSolvable subgroup] :
    signalizerMcBrideHypothesisB prime subgroup := by
  refine ⟨prime_prime, coprime, ?_⟩
  intro numerator denominator numerator_le _ normal simple nonabelian
  let := simple
  obtain ⟨first, second, not_commute⟩ := nonabelian
  exact (not_commute
    (solvable_simple_section_commutative numerator_le first second)).elim

theorem elementary_abelian_isPGroup (prime : ℕ) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) : IsPGroup prime actor := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro element
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using elementary.2 element element.property

theorem elementary_abelian_of_le (prime : ℕ)
    {actor subgroup : Subgroup GroupType} (elementary : IsElemAbelian prime actor)
    (contained : subgroup ≤ actor) : IsElemAbelian prime subgroup := by
  let := elementary.1
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · intro first second
    apply Subtype.ext
    exact congrArg (fun element : actor => (element : GroupType))
      (mul_comm' (⟨first, contained first.property⟩ : actor)
        (⟨second, contained second.property⟩ : actor))
  · intro element member
    exact elementary.2 element (contained member)

theorem signalizerFunctorEk_nonempty [Finite GroupType] (prime rank : ℕ)
    (prime_prime : prime.Prime) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ rank ≤ Nat.card actor) :
    (signalizerFunctorEk prime rank actor).Nonempty := by
  obtain ⟨internal, internal_card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card prime_prime
      (elementary_abelian_isPGroup prime actor elementary) large
  refine ⟨internal.map actor.subtype, ?_, ?_⟩
  · rintro element ⟨internal_element, _, rfl⟩
    exact internal_element.property
  · exact (Subgroup.card_map_of_injective actor.subtype_injective).trans internal_card

end CFSG.SignalizerFunctor.Helpers
