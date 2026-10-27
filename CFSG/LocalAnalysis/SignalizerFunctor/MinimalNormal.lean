module

public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem normal_of_characteristic_subgroup (parent : Subgroup GroupType) [parent.Normal]
    (internal : Subgroup parent) [internal.Characteristic] :
    (internal.map parent.subtype).Normal := by
  constructor
  rintro element ⟨representative, member, rfl⟩ conjugator
  refine ⟨MulAut.conjNormal conjugator representative, ?_, rfl⟩
  exact Subgroup.characteristic_iff_le_comap.mp inferInstance
    (MulAut.conjNormal conjugator) member

theorem solvable_minimal_normal_commutative [Finite GroupType] [Group.IsSolvable GroupType]
    (subgroup : Subgroup GroupType) [subgroup.Normal] (nontrivial : subgroup ≠ ⊥)
    (minimal : ∀ smaller : Subgroup GroupType, smaller ≤ subgroup → smaller.Normal →
      smaller ≠ ⊥ → smaller = subgroup) : IsMulCommutative subgroup := by
  let derived := (commutator subgroup).map subgroup.subtype
  have derived_normal : derived.Normal := normal_of_characteristic_subgroup subgroup _
  have derived_trivial : derived = ⊥ := by
    by_contra not_trivial
    have equality := minimal derived (Subgroup.map_subtype_le _) derived_normal not_trivial
    have cardinality := congrArg (fun target : Subgroup GroupType => Nat.card target) equality
    change Nat.card ((commutator subgroup).map subgroup.subtype) = Nat.card subgroup
      at cardinality
    rw [Subgroup.card_map_of_injective subgroup.subtype_injective] at cardinality
    let : Nontrivial subgroup := (Subgroup.nontrivial_iff_ne_bot subgroup).mpr nontrivial
    have smaller : Nat.card (commutator subgroup) < Nat.card subgroup := by
      apply lt_of_le_of_ne (commutator subgroup).card_le_card_group
      intro equal_card
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial subgroup).ne
        ((commutator subgroup).card_eq_iff_eq_top.mp equal_card)
    exact smaller.ne cardinality
  apply (commutator_eq_bot_iff subgroup).mp
  exact (Subgroup.map_eq_bot_iff_of_injective _ subgroup.subtype_injective).mp derived_trivial

theorem solvable_minimal_normal_elementary [Finite GroupType] [Group.IsSolvable GroupType]
    (subgroup : Subgroup GroupType) [subgroup.Normal] (nontrivial : subgroup ≠ ⊥)
    (minimal : ∀ smaller : Subgroup GroupType, smaller ≤ subgroup → smaller.Normal →
      smaller ≠ ⊥ → smaller = subgroup) :
    ∃ prime : ℕ, prime.Prime ∧ IsElemAbelian prime subgroup := by
  let commutative := solvable_minimal_normal_commutative subgroup nontrivial minimal
  let := commutative
  let _commGroup : CommGroup subgroup := { subgroup.toGroup with mul_comm := mul_comm' }
  have cardinality_nontrivial : Nat.card subgroup ≠ 1 := by
    intro cardinality
    exact nontrivial ((Subgroup.eq_bot_iff_card subgroup).mpr cardinality)
  obtain ⟨prime, prime_prime, divides⟩ := Nat.exists_prime_and_dvd cardinality_nontrivial
  let : Fact prime.Prime := ⟨prime_prime⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' (G := subgroup) prime divides
  let kernel := (powMonoidHom (α := subgroup) prime).ker
  have kernel_characteristic : kernel.Characteristic := by
    apply Subgroup.characteristic_iff_le_comap.mpr
    intro equiv representative member
    change representative ^ prime = 1 at member
    change equiv representative ^ prime = 1
    rw [← map_pow, member, map_one]
  let := kernel_characteristic
  let embedded := kernel.map subgroup.subtype
  have embedded_normal : embedded.Normal := normal_of_characteristic_subgroup subgroup kernel
  have element_member : element ∈ kernel := by
    change element ^ prime = 1
    rw [← element_order]
    exact pow_orderOf_eq_one element
  have embedded_nontrivial : embedded ≠ ⊥ := by
    intro trivial
    have member := Subgroup.mem_map_of_mem subgroup.subtype element_member
    change element.val ∈ embedded at member
    rw [trivial] at member
    have identity : element = 1 := Subtype.ext member
    exact prime_prime.ne_one (element_order.symm.trans (orderOf_eq_one_iff.mpr identity))
  have embedded_equal := minimal embedded (Subgroup.map_subtype_le _) embedded_normal
    embedded_nontrivial
  refine ⟨prime, prime_prime, commutative, ?_⟩
  intro representative member
  have embedded_member : representative ∈ embedded := by
    rw [embedded_equal]
    exact member
  obtain ⟨internal, internal_member, mapped⟩ := embedded_member
  have killed : internal ^ prime = 1 := internal_member
  have killed_ambient := congrArg (fun internal : subgroup => (internal : GroupType)) killed
  change internal.val ^ prime = 1 at killed_ambient
  change internal.val = representative at mapped
  rwa [mapped] at killed_ambient

theorem solvable_minimal_normal_exists [Finite GroupType] [Nontrivial GroupType]
    [Group.IsSolvable GroupType] :
    ∃ subgroup : Subgroup GroupType, subgroup.Normal ∧ subgroup ≠ ⊥ ∧
      (∀ smaller : Subgroup GroupType, smaller ≤ subgroup → smaller.Normal →
        smaller ≠ ⊥ → smaller = subgroup) ∧
      ∃ prime rank : ℕ, prime.Prime ∧ 1 ≤ rank ∧ IsElemAbelian prime subgroup ∧
        Nat.card subgroup = prime ^ rank := by
  classical
  let property : Subgroup GroupType → Prop := fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥
  have whole_property : property ⊤ := ⟨inferInstance, top_ne_bot⟩
  obtain ⟨subgroup, _, minimal⟩ := Finite.exists_le_minimal whole_property
  have subgroup_normal := minimal.prop.1
  let := subgroup_normal
  have minimal_normal : ∀ smaller : Subgroup GroupType, smaller ≤ subgroup → smaller.Normal →
      smaller ≠ ⊥ → smaller = subgroup := by
    intro smaller contained normal nontrivial
    exact minimal.eq_of_le ⟨normal, nontrivial⟩ contained
  obtain ⟨prime, prime_prime, elementary⟩ := solvable_minimal_normal_elementary subgroup
    minimal.prop.2 minimal_normal
  let : Fact prime.Prime := ⟨prime_prime⟩
  obtain ⟨rank, cardinality⟩ := IsPGroup.iff_card.mp
    (elementary_abelian_isPGroup prime subgroup elementary)
  have positive_rank : 1 ≤ rank := by
    by_contra small
    have zero_rank : rank = 0 := by omega
    rw [zero_rank, pow_zero] at cardinality
    exact minimal.prop.2 ((Subgroup.eq_bot_iff_card subgroup).mpr cardinality)
  exact ⟨subgroup, subgroup_normal, minimal.prop.2, minimal_normal, prime, rank, prime_prime,
    positive_rank, elementary, cardinality⟩

end CFSG.SignalizerFunctor.Helpers
