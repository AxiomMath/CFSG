module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductCore
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableFitting

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem corefree_hall_product_normalized_complement_trivial
    (prime : ℕ) (prime_prime : prime.Prime) (complement factor target : Subgroup GroupType)
    (complement_coprime : Nat.Coprime prime (Nat.card complement))
    (factor_pgroup : IsPGroup prime factor) (whole : subgroupProduct complement factor = Set.univ)
    (corefree : complement.normalCore = ⊥) (target_coprime : Nat.Coprime prime (Nat.card target))
    (normalized : factor ≤ Subgroup.normalizer (target : Set GroupType)) : target = ⊥ := by
  have contained := hall_product_normalized_complement_le_core prime prime_prime complement factor target
    complement_coprime factor_pgroup whole target_coprime normalized
  rw [corefree] at contained
  exact le_bot_iff.mp contained

theorem corefree_hall_product_fitting_le_factor
    (prime : ℕ) (prime_prime : prime.Prime) (complement factor parent : Subgroup GroupType)
    (complement_coprime : Nat.Coprime prime (Nat.card complement))
    (factor_pgroup : IsPGroup prime factor) (whole : subgroupProduct complement factor = Set.univ)
    (corefree : complement.normalCore = ⊥) (factor_le : factor ≤ parent) :
    (fittingSubgroup (GroupType := parent)).map parent.subtype ≤ factor := by
  obtain ⟨ambientSylow, sylow_eq⟩ :=
    (hall_product_orders prime prime_prime complement factor complement_coprime factor_pgroup whole).2.2.2
  have ambient_le : (ambientSylow : Subgroup GroupType) ≤ parent := by
    rw [sylow_eq]
    exact factor_le
  have fitting_prime_le : ∀ other : {other : ℕ // other.Prime},
      (primeSetCore (GroupType := parent) {other.val}).map parent.subtype ≤ factor := by
    intro other
    let internal := primeSetCore (GroupType := parent) {other.val}
    let embedded := internal.map parent.subtype
    let _internalCharacteristic : internal.Characteristic := prime_set_core_characteristic {other.val}
    have normalized : factor ≤ Subgroup.normalizer (embedded : Set GroupType) :=
      factor_le.trans (characteristic_subgroup_map_normalized parent parent Subgroup.le_normalizer internal)
    by_cases same : other.val = prime
    · let _internalNormal : internal.Normal := prime_set_core_normal {other.val}
      have internal_pgroup : IsPGroup prime internal := by
        rw [← same]
        exact prime_core_isPGroup other.val other.property
      have contained := internal_pgroup.le_sylow_of_normal (ambientSylow.subtype ambient_le)
      rw [Sylow.coe_subtype] at contained
      have mapped_le := Subgroup.map_mono (f := parent.subtype) contained
      rwa [Subgroup.subgroupOf_map_subtype, sylow_eq, inf_eq_left.mpr factor_le] at mapped_le
    · have coprime : Nat.Coprime prime (Nat.card embedded) := by
        rw [Subgroup.card_map_of_injective parent.subtype_injective]
        exact prime_coprime_pgroup_card prime other.val prime_prime other.property (Ne.symm same)
          (prime_core_isPGroup other.val other.property)
      have trivial := corefree_hall_product_normalized_complement_trivial prime prime_prime complement factor
        embedded complement_coprime factor_pgroup whole corefree coprime normalized
      change embedded ≤ factor
      rw [trivial]
      exact bot_le
  rw [fitting_subgroup_eq_prime_cores, Subgroup.map_iSup]
  exact iSup_le fitting_prime_le

theorem corefree_abelian_hall_product_fitting_eq_factor
    (prime : ℕ) (prime_prime : prime.Prime) (complement factor parent : Subgroup GroupType)
    (complement_coprime : Nat.Coprime prime (Nat.card complement))
    (factor_pgroup : IsPGroup prime factor) (whole : subgroupProduct complement factor = Set.univ)
    (corefree : complement.normalCore = ⊥) (factor_le : factor ≤ parent)
    (abelian : IsMulCommutative factor) (solvable : Group.IsSolvable parent) :
    (fittingSubgroup (GroupType := parent)).map parent.subtype = factor ∧
      (factor.subgroupOf parent).Normal := by
  let := solvable
  let := abelian
  have fitting_le := corefree_hall_product_fitting_le_factor prime prime_prime complement factor parent
    complement_coprime factor_pgroup whole corefree factor_le
  have factor_le_fitting : factor ≤ (fittingSubgroup (GroupType := parent)).map parent.subtype := by
    intro element member
    have centralizes : (⟨element, factor_le member⟩ : parent) ∈
        Subgroup.centralizer (fittingSubgroup (GroupType := parent) : Set parent) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro other other_member
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.le_centralizer factor member) other.val
        (fitting_le (Subgroup.mem_map_of_mem parent.subtype other_member))
    exact Subgroup.mem_map_of_mem parent.subtype (solvable_fitting_centralizer_le centralizes)
  have equal := le_antisymm fitting_le factor_le_fitting
  refine ⟨equal, ?_⟩
  have internal_eq : factor.subgroupOf parent = fittingSubgroup := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr factor_le]
    exact equal.symm
  rw [internal_eq]
  exact fitting_subgroup_normal

end CFSG.SignalizerFunctor.Helpers
