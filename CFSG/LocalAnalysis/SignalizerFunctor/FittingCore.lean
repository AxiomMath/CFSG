module

public import CFSG.LocalAnalysis.SignalizerFunctor.SylowGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def fittingSubgroup : Subgroup GroupType :=
  ⨆ (candidate : Subgroup GroupType) (_ : candidate.Normal ∧ Group.IsNilpotent candidate), candidate

theorem fitting_subgroup_contains (candidate : Subgroup GroupType)
    (normal : candidate.Normal) (nilpotent : Group.IsNilpotent candidate) :
    candidate ≤ fittingSubgroup :=
  le_iSup_of_le candidate (le_iSup_of_le ⟨normal, nilpotent⟩ le_rfl)

theorem fitting_subgroup_normal : (fittingSubgroup (GroupType := GroupType)).Normal := by
  let candidates := {candidate : Subgroup GroupType // candidate.Normal ∧ Group.IsNilpotent candidate}
  let _normals : ∀ candidate : candidates, candidate.val.Normal := fun candidate => candidate.property.1
  have normal : (⨆ candidate : candidates, candidate.val).Normal := inferInstance
  have equal : (⨆ candidate : candidates, candidate.val) = fittingSubgroup := iSup_subtype
  rwa [equal] at normal

theorem fitting_subgroup_map_isomorphism {ImageType : Type imageUniverse} [Group ImageType]
    (equivalence : GroupType ≃* ImageType) :
    (fittingSubgroup (GroupType := GroupType)).map equivalence.toMonoidHom = fittingSubgroup := by
  have map_le : ∀ {Source : Type groupUniverse} [Group Source]
      {Target : Type imageUniverse} [Group Target] (isomorphism : Source ≃* Target),
      (fittingSubgroup (GroupType := Source)).map isomorphism.toMonoidHom ≤ fittingSubgroup := by
    intro Source _ Target _ isomorphism
    unfold fittingSubgroup
    simp only [Subgroup.map_iSup]
    apply iSup_le
    intro candidate
    apply iSup_le
    intro properties
    apply fitting_subgroup_contains
    · exact properties.1.map isomorphism.toMonoidHom isomorphism.surjective
    · let := properties.2
      exact Group.nilpotent_of_mulEquiv (candidate.equivMapOfInjective isomorphism.toMonoidHom
        isomorphism.injective)
  apply le_antisymm (map_le equivalence)
  have inverse_le : (fittingSubgroup (GroupType := ImageType)).map equivalence.symm.toMonoidHom ≤
      fittingSubgroup := by
    unfold fittingSubgroup
    simp only [Subgroup.map_iSup]
    apply iSup_le
    intro candidate
    apply iSup_le
    intro properties
    apply fitting_subgroup_contains
    · exact properties.1.map equivalence.symm.toMonoidHom equivalence.symm.surjective
    · let := properties.2
      exact Group.nilpotent_of_mulEquiv (candidate.equivMapOfInjective equivalence.symm.toMonoidHom
        equivalence.symm.injective)
  have mapped_le := Subgroup.map_mono (f := equivalence.toMonoidHom) inverse_le
  rw [Subgroup.map_map] at mapped_le
  have identity : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom = MonoidHom.id ImageType := by
    ext element
    exact equivalence.apply_symm_apply element
  rwa [identity, Subgroup.map_id] at mapped_le

theorem fitting_subgroup_characteristic : (fittingSubgroup (GroupType := GroupType)).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr fitting_subgroup_map_isomorphism

theorem nilpotent_sup_of_centralizing (first second : Subgroup GroupType)
    (centralizes : first ≤ Subgroup.centralizer (second : Set GroupType))
    (first_nilpotent : Group.IsNilpotent first) (second_nilpotent : Group.IsNilpotent second) :
    Group.IsNilpotent (first ⊔ second : Subgroup GroupType) := by
  let := first_nilpotent
  let := second_nilpotent
  have normalizes : second ≤ Subgroup.normalizer (first : Set GroupType) :=
    (Subgroup.le_centralizer_iff.mp centralizes).trans (Subgroup.centralizer_le_normalizer _)
  let multiplication : first × second →* (first ⊔ second : Subgroup GroupType) :=
    { toFun := fun pair => ⟨pair.1.val * pair.2.val,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left pair.1.property) (Subgroup.mem_sup_right pair.2.property)⟩
      map_one' := Subtype.ext (one_mul 1)
      map_mul' := by
        intro firstPair secondPair
        apply Subtype.ext
        change (firstPair.1.val * secondPair.1.val) * (firstPair.2.val * secondPair.2.val) =
          (firstPair.1.val * firstPair.2.val) * (secondPair.1.val * secondPair.2.val)
        have commutes : secondPair.1.val * firstPair.2.val = firstPair.2.val * secondPair.1.val :=
          (Subgroup.mem_centralizer_iff.mp (centralizes secondPair.1.property)
            firstPair.2.val firstPair.2.property).symm
        calc
          _ = firstPair.1.val * (secondPair.1.val * firstPair.2.val) * secondPair.2.val := by group
          _ = firstPair.1.val * (firstPair.2.val * secondPair.1.val) * secondPair.2.val := by rw [commutes]
          _ = _ := by group }
  have surjective : Function.Surjective multiplication := by
    intro element
    obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
      (mem_sup_of_normalizing first second normalizes element.val).mp element.property
    exact ⟨(⟨firstElement, first_member⟩, ⟨secondElement, second_member⟩), Subtype.ext product⟩
  exact Group.nilpotent_of_surjective multiplication surjective

theorem distinct_prime_cores_centralize [Finite GroupType]
    (firstPrime secondPrime : ℕ) (first_prime : firstPrime.Prime) (second_prime : secondPrime.Prime)
    (distinct : firstPrime ≠ secondPrime) :
    primeSetCore (GroupType := GroupType) {firstPrime} ≤
      Subgroup.centralizer (primeSetCore (GroupType := GroupType) {secondPrime} : Set GroupType) := by
  let _firstNormal := prime_set_core_normal (GroupType := GroupType) {firstPrime}
  let _secondNormal := prime_set_core_normal (GroupType := GroupType) {secondPrime}
  have disjoint := IsPGroup.disjoint_of_coprime
    (prime_core_isPGroup (GroupType := GroupType) firstPrime first_prime)
    (prime_core_isPGroup (GroupType := GroupType) secondPrime second_prime)
    ((Nat.coprime_primes first_prime second_prime).mpr distinct)
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  exact le_bot_iff.mp ((Subgroup.commutator_le_inf _ _).trans disjoint.eq_bot.le)

theorem normal_nilpotent_le_prime_cores [Finite GroupType]
    (candidate : Subgroup GroupType) [candidate.Normal] [Group.IsNilpotent candidate] :
    candidate ≤ ⨆ prime : {prime : ℕ // prime.Prime}, primeSetCore {prime.val} := by
  let combined : Subgroup GroupType := ⨆ prime : {prime : ℕ // prime.Prime}, primeSetCore {prime.val}
  have contains : ∀ prime : ℕ, prime.Prime →
      ∃ sylow : Sylow prime candidate, (sylow : Subgroup candidate) ≤ combined.subgroupOf candidate := by
    intro prime prime_prime
    let : Fact prime.Prime := ⟨prime_prime⟩
    let sylow : Sylow prime candidate := Classical.choice inferInstance
    let _characteristic : (sylow : Subgroup candidate).Characteristic :=
      sylow.characteristic_of_normal inferInstance
    have embedded_normal := normal_of_characteristic_subgroup candidate (sylow : Subgroup candidate)
    have embedded_supported := (prime_supported_singleton_iff_pgroup prime prime_prime _).mpr
      (sylow.isPGroup'.map candidate.subtype)
    have embedded_le := (prime_set_core_contains {prime} _ embedded_normal embedded_supported).trans
      (le_iSup (fun prime : {prime : ℕ // prime.Prime} => primeSetCore {prime.val}) ⟨prime, prime_prime⟩)
    refine ⟨sylow, ?_⟩
    intro element member
    exact embedded_le (Subgroup.mem_map_of_mem candidate.subtype member)
  have equal := eq_top_of_sylow_containment (combined.subgroupOf candidate) contains
  intro element member
  have internal : (⟨element, member⟩ : candidate) ∈ combined.subgroupOf candidate := by
    rw [equal]
    trivial
  exact internal

theorem fitting_subgroup_eq_prime_cores [Finite GroupType] :
    fittingSubgroup (GroupType := GroupType) =
      ⨆ prime : {prime : ℕ // prime.Prime}, primeSetCore {prime.val} := by
  apply le_antisymm
  · apply iSup_le
    intro candidate
    apply iSup_le
    intro properties
    let := properties.1
    let := properties.2
    exact normal_nilpotent_le_prime_cores candidate
  · apply iSup_le
    intro prime
    let : Fact prime.val.Prime := ⟨prime.property⟩
    exact fitting_subgroup_contains _ (prime_set_core_normal {prime.val})
      (prime_core_isPGroup prime.val prime.property).isNilpotent

theorem prime_core_trivial_of_not_dvd [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (not_divides : ¬ prime ∣ Nat.card GroupType) :
    primeSetCore (GroupType := GroupType) {prime} = ⊥ := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  rcases (prime_core_isPGroup (GroupType := GroupType) prime prime_prime).card_eq_or_dvd with equal | divides
  · exact (Subgroup.eq_bot_iff_card _).mpr equal
  · exact (not_divides (divides.trans (Subgroup.card_subgroup_dvd_card _))).elim

theorem finite_prime_core_join_nilpotent [Finite GroupType]
    (primes : Finset ℕ) (all_prime : ∀ prime ∈ primes, prime.Prime) :
    Group.IsNilpotent (primes.sup (fun prime => primeSetCore (GroupType := GroupType) {prime}) :
      Subgroup GroupType) := by
  classical
  induction primes using Finset.induction_on with
  | empty =>
    change Group.IsNilpotent (⊥ : Subgroup GroupType)
    infer_instance
  | @insert prime primes not_member induction_hypothesis =>
    have prime_prime := all_prime prime (Finset.mem_insert_self _ _)
    have members_prime : ∀ other ∈ primes, other.Prime := fun other member =>
      all_prime other (Finset.mem_insert_of_mem member)
    have centralizes : primeSetCore (GroupType := GroupType) {prime} ≤
        Subgroup.centralizer
          ((primes.sup (fun other => primeSetCore {other}) : Subgroup GroupType) : Set GroupType) := by
      apply Subgroup.le_centralizer_iff.mpr
      apply Finset.sup_le
      intro other member
      apply distinct_prime_cores_centralize other prime (members_prime other member) prime_prime
      intro equal
      exact not_member (equal ▸ member)
    rw [Finset.sup_insert]
    let : Fact prime.Prime := ⟨prime_prime⟩
    exact nilpotent_sup_of_centralizing _ _ centralizes
      (prime_core_isPGroup prime prime_prime).isNilpotent (induction_hypothesis members_prime)

theorem fitting_subgroup_eq_finite_prime_cores [Finite GroupType] :
    fittingSubgroup (GroupType := GroupType) =
      (Nat.card GroupType).primeFactors.sup (fun prime => primeSetCore {prime}) := by
  rw [fitting_subgroup_eq_prime_cores]
  apply le_antisymm
  · apply iSup_le
    intro prime
    by_cases divides : prime.val ∣ Nat.card GroupType
    · exact Finset.le_sup (f := fun prime => primeSetCore {prime})
        (prime.property.mem_primeFactors divides Nat.card_pos.ne')
    · rw [prime_core_trivial_of_not_dvd prime.val prime.property divides]
      exact bot_le
  · apply Finset.sup_le
    intro prime member
    exact le_iSup (fun prime : {prime : ℕ // prime.Prime} => primeSetCore {prime.val})
      ⟨prime, Nat.prime_of_mem_primeFactors member⟩

theorem fitting_subgroup_nilpotent [Finite GroupType] :
    Group.IsNilpotent (fittingSubgroup (GroupType := GroupType)) := by
  rw [fitting_subgroup_eq_finite_prime_cores]
  exact finite_prime_core_join_nilpotent (GroupType := GroupType) _
    (fun _ member => Nat.prime_of_mem_primeFactors member)

end CFSG.SignalizerFunctor.Helpers
