module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedGrowth
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerConditions
public import CFSG.LocalAnalysis.SignalizerFunctor.ActionPrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalNilpotentPrimeCore

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def conjugatePairSubgroup (element conjugator : GroupType) : Subgroup GroupType :=
  Subgroup.zpowers element ⊔ conjugateSubgroup conjugator (Subgroup.zpowers element)

theorem conjugate_pair_subgroup_map {ImageType : Type imageUniverse} [Group ImageType]
    (homomorphism : GroupType →* ImageType) (element conjugator : GroupType) :
    (conjugatePairSubgroup element conjugator).map homomorphism =
      conjugatePairSubgroup (homomorphism element) (homomorphism conjugator) := by
  unfold conjugatePairSubgroup
  rw [Subgroup.map_sup, conjugate_subgroup_map, MonoidHom.map_zpowers]

theorem solvable_conjugate_pair_core [Finite GroupType] [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (element : GroupType)
    (pairs : ∀ conjugator : GroupType, IsPGroup prime (conjugatePairSubgroup element conjugator)) :
    element ∈ primeSetCore {prime} := by
  classical
  let : Fact prime.Prime := ⟨prime_prime⟩
  suffices general : ∀ order : ℕ,
      ∀ (TargetType : Type groupUniverse) [Group TargetType] [Finite TargetType] [Group.IsSolvable TargetType],
        Nat.card TargetType = order → ∀ targetElement : TargetType,
          (∀ conjugator : TargetType, IsPGroup prime (conjugatePairSubgroup targetElement conjugator)) →
          targetElement ∈ primeSetCore {prime} by
    exact general (Nat.card GroupType) GroupType rfl element pairs
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro TargetType _ _ _ target_card targetElement target_pairs
    rcases subsingleton_or_nontrivial TargetType with trivial | nontrivial
    · let := trivial
      rw [Subsingleton.elim targetElement 1]
      exact Subgroup.one_mem _
    · let := nontrivial
      obtain ⟨normal, normal_property, normal_nontrivial, _, other, rank, other_prime, _, elementary, _⟩ :=
        solvable_minimal_normal_exists (GroupType := TargetType)
      let _normal := normal_property
      let projection := QuotientGroup.mk' normal
      have quotient_pairs : ∀ conjugator : TargetType ⧸ normal,
          IsPGroup prime (conjugatePairSubgroup (projection targetElement) conjugator) := by
        intro conjugator
        obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective normal conjugator
        have image_pgroup := (target_pairs representative).map projection
        rwa [conjugate_pair_subgroup_map] at image_pgroup
      have quotient_smaller : Nat.card (TargetType ⧸ normal) < order := by
        rw [← target_card]
        exact normal_quotient_card_strict normal normal_nontrivial
      have quotient_member := induction_hypothesis (Nat.card (TargetType ⧸ normal)) quotient_smaller
        (TargetType ⧸ normal) rfl (projection targetElement) quotient_pairs
      let actionCore := quotientActionPrimeCore prime normal
      let _actionCoreNormal := quotient_action_prime_core_normal prime normal
      have action_core_member : targetElement ∈ actionCore := quotient_member
      have normal_pgroup := elementary_abelian_isPGroup other normal elementary
      by_cases same : other = prime
      · have prime_pgroup : IsPGroup prime normal := same ▸ normal_pgroup
        have equality := quotient_action_prime_core_eq_prime_core prime prime_prime normal prime_pgroup
        change targetElement ∈ quotientActionPrimeCore prime normal at action_core_member
        rwa [equality] at action_core_member
      · have normal_coprime := prime_coprime_pgroup_card prime other prime_prime other_prime (Ne.symm same)
          normal_pgroup
        have centralizes : targetElement ∈ Subgroup.centralizer (normal : Set TargetType) := by
          apply Subgroup.mem_centralizer_iff.mpr
          intro normalElement normal_member
          let difference := normalElement * targetElement * normalElement⁻¹ * targetElement⁻¹
          have difference_normal : difference ∈ normal := by
            have conjugated := Subgroup.Normal.conj_mem normal_property normalElement⁻¹
              (normal.inv_mem normal_member) targetElement
            simpa only [difference, mul_assoc] using normal.mul_mem normal_member conjugated
          have difference_pair : difference ∈ conjugatePairSubgroup targetElement normalElement := by
            exact (conjugatePairSubgroup targetElement normalElement).mul_mem
              (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (MulAut.conj normalElement).toMonoidHom
                (Subgroup.mem_zpowers targetElement)))
              (Subgroup.mem_sup_left ((Subgroup.zpowers targetElement).inv_mem (Subgroup.mem_zpowers targetElement)))
          have intersection_pgroup := (target_pairs normalElement).to_le
            (show normal ⊓ conjugatePairSubgroup targetElement normalElement ≤
              conjugatePairSubgroup targetElement normalElement from inf_le_right)
          have intersection_coprime := normal_coprime.of_dvd_right
            (Subgroup.card_dvd_of_le (show normal ⊓ conjugatePairSubgroup targetElement normalElement ≤ normal from
              inf_le_left))
          have intersection_bot : normal ⊓ conjugatePairSubgroup targetElement normalElement = ⊥ := by
            rcases intersection_pgroup.card_eq_or_dvd with cardinality | divides
            · exact Subgroup.card_eq_one.mp cardinality
            · exact (prime_prime.coprime_iff_not_dvd.mp intersection_coprime divides).elim
          have difference_one : difference = 1 := by
            have contained : difference ∈ normal ⊓ conjugatePairSubgroup targetElement normalElement :=
              ⟨difference_normal, difference_pair⟩
            rwa [intersection_bot, Subgroup.mem_bot] at contained
          calc
            normalElement * targetElement = difference * targetElement * normalElement := by
              dsimp only [difference]
              group
            _ = targetElement * normalElement := by rw [difference_one, one_mul]
        let centralizer := actionCore ⊓ Subgroup.centralizer (normal : Set TargetType)
        have centralizer_normal : centralizer.Normal := inferInstance
        have normal_le : normal ≤ centralizer := by
          apply le_inf (kernel_le_quotient_action_prime_core prime normal)
          let := elementary.1
          exact Subgroup.le_centralizer normal
        have normal_central : normal ≤ Subgroup.centralizer (centralizer : Set TargetType) :=
          Subgroup.le_centralizer_iff.mp inf_le_right
        have centralizer_image_pgroup : IsPGroup prime (centralizer.map projection) :=
          (quotient_action_prime_core_image_pgroup prime prime_prime normal).to_le
            (Subgroup.map_mono inf_le_left)
        let _nilpotent := central_kernel_pgroup_image_nilpotent prime prime_prime centralizer normal
          normal_central normal_property centralizer_image_pgroup
        let _centralizerNormal := centralizer_normal
        have element_centralizer : targetElement ∈ centralizer := ⟨action_core_member, centralizes⟩
        have cyclic_le : Subgroup.zpowers targetElement ≤ centralizer :=
          Subgroup.zpowers_le.mpr element_centralizer
        have cyclic_pgroup : IsPGroup prime (Subgroup.zpowers targetElement) :=
          (target_pairs 1).to_le le_sup_left
        exact normal_nilpotent_prime_subgroup_le_core prime prime_prime centralizer _ cyclic_le cyclic_pgroup
          (Subgroup.mem_zpowers targetElement)

end CFSG.SignalizerFunctor.Helpers
