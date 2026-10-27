module

public import CFSG.LocalAnalysis.SignalizerFunctor.FrattiniAutomorphismKernel

public section

universe groupUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem automorphism_preserves_frattini (automorphism : MulAut GroupType)
    (element : GroupType) (member : element ∈ frattini GroupType) :
    automorphism • element ∈ frattini GroupType :=
  Subgroup.characteristic_iff_le_comap.mp inferInstance automorphism member

@[expose] def frattiniQuotientAutomorphism (GroupType : Type groupUniverse) [Group GroupType] :
    MulAut GroupType →* MulAut (GroupType ⧸ frattini GroupType) :=
  let _action := invariantQuotientAction (frattini GroupType) automorphism_preserves_frattini
  MulDistribMulAction.toMulAut (MulAut GroupType) (GroupType ⧸ frattini GroupType)

theorem frattini_quotient_automorphism_equivariant (automorphism : MulAut GroupType) (element : GroupType) :
    frattiniQuotientAutomorphism GroupType automorphism (QuotientGroup.mk' (frattini GroupType) element) =
      QuotientGroup.mk' (frattini GroupType) (automorphism element) := by
  let _action := invariantQuotientAction (frattini GroupType) automorphism_preserves_frattini
  exact (invariant_quotient_equivariant (frattini GroupType) automorphism_preserves_frattini
    automorphism element).symm

theorem frattini_quotient_automorphism_kernel : (frattiniQuotientAutomorphism GroupType).ker =
    frattiniAutomorphismKernel GroupType := by
  ext automorphism
  constructor
  · intro member element
    have identity : frattiniQuotientAutomorphism GroupType automorphism = 1 := member
    have equal := congrArg (fun action => action (QuotientGroup.mk' (frattini GroupType) element)) identity
    rwa [frattini_quotient_automorphism_equivariant, MulAut.one_apply] at equal
  · intro member
    apply MulEquiv.ext
    intro element
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective (frattini GroupType) element
    rw [frattini_quotient_automorphism_equivariant]
    exact member representative

theorem quadratic_automorphism_quotient (automorphism : MulAut GroupType)
    (quadratic : ∀ element : GroupType,
      automorphism (element⁻¹ * automorphism element) = element⁻¹ * automorphism element)
    (element : GroupType ⧸ frattini GroupType) :
    frattiniQuotientAutomorphism GroupType automorphism
      (element⁻¹ * frattiniQuotientAutomorphism GroupType automorphism element) =
      element⁻¹ * frattiniQuotientAutomorphism GroupType automorphism element := by
  obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective (frattini GroupType) element
  rw [frattini_quotient_automorphism_equivariant, ← map_inv, ← map_mul,
    frattini_quotient_automorphism_equivariant, quadratic]

variable [Finite GroupType]

theorem frattini_quotient_automorphism_kernel_pgroup (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType) : IsPGroup prime (frattiniQuotientAutomorphism GroupType).ker := by
  rw [frattini_quotient_automorphism_kernel]
  exact frattini_automorphism_kernel_pgroup prime prime_prime pgroup

theorem faithful_frattini_action_kernel_pgroup (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType) {ActorType : Type actorUniverse} [Group ActorType]
    (action : ActorType →* MulAut GroupType) (faithful : Function.Injective action) :
    IsPGroup prime ((frattiniQuotientAutomorphism GroupType).comp action).ker := by
  change IsPGroup prime ((frattiniQuotientAutomorphism GroupType).ker.comap action)
  exact (frattini_quotient_automorphism_kernel_pgroup prime prime_prime pgroup).comap_of_injective action faithful

end CFSG.SignalizerFunctor.Helpers
