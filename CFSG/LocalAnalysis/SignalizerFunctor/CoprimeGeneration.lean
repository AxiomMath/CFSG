module

public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.LocalAnalysis.SignalizerFunctor.SylowGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableGeneration

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

theorem coprime_cyclic_quotient_generation
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType)) :
    (⨆ (actorSubgroup : Subgroup ActorType) (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
      FixedPoints.subgroup actorSubgroup GroupType) = ⊤ := by
  classical
  let generated : Subgroup GroupType :=
    ⨆ (actorSubgroup : Subgroup ActorType) (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
      FixedPoints.subgroup actorSubgroup GroupType
  change generated = ⊤
  apply eq_top_of_sylow_containment
  intro sylowPrime sylowPrime_prime
  let : Fact sylowPrime.Prime := ⟨sylowPrime_prime⟩
  obtain ⟨sylow, fixed⟩ := invariant_sylow_exists prime sylowPrime prime_prime
    sylowPrime_prime actor_pgroup coprime
  let subgroup : Subgroup GroupType := sylow
  have invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup := by
    intro actorElement element member
    have image_fixed : actorElement • subgroup = subgroup := by
      rw [← Sylow.pointwise_smul_def, fixed]
    rw [← image_fixed]
    exact Subgroup.smul_mem_pointwise_smul element actorElement subgroup member
  let _subgroupAction := invariantSubgroupAction subgroup invariant
  let _nilpotent : Group.IsNilpotent subgroup := sylow.isPGroup'.isNilpotent
  have subgroup_coprime : Nat.Coprime prime (Nat.card subgroup) :=
    coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card subgroup)
  have subgroup_generated := solvable_cyclic_quotient_generation prime prime_prime
    ActorType actor_pgroup subgroup subgroup_coprime
  refine ⟨sylow, ?_⟩
  change subgroup ≤ generated
  rw [← subgroup.subtype_range, MonoidHom.range_eq_map, ← subgroup_generated]
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro actorSubgroup
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro cyclic
  exact (invariant_subgroup_fixed_points_le subgroup invariant actorSubgroup).trans
    (le_iSup_of_le actorSubgroup (le_iSup_of_le cyclic le_rfl))

end CFSG.SignalizerFunctor.Helpers
