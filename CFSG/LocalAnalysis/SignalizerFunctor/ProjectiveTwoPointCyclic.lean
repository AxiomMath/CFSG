module

public import CFSG.LocalAnalysis.SignalizerFunctor.LinearEigenvalueCharacters

public section

universe fieldUniverse vectorUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]
variable {ActorType : Type actorUniverse} [Group ActorType] [Finite ActorType]

theorem linear_projective_two_point_image_cyclic [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (first second : Projectivization FieldType VectorType) (distinct : first ≠ second)
    (first_fixed : ∀ actor : ActorType, projectiveLinearAction (action actor) first = first)
    (second_fixed : ∀ actor : ActorType, projectiveLinearAction (action actor) second = second) :
    IsCyclic (projectiveLinearAction.comp action).range := by
  classical
  have first_invariant : ∀ actor : ActorType, ∃ scalar : FieldType,
      action actor first.rep = scalar • first.rep := by
    intro actor
    apply (projective_linear_fixed_iff_eigenvector (action actor) first.rep first.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using first_fixed actor
  have second_invariant : ∀ actor : ActorType, ∃ scalar : FieldType,
      action actor second.rep = scalar • second.rep := by
    intro actor
    apply (projective_linear_fixed_iff_eigenvector (action actor) second.rep second.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using second_fixed actor
  let ratio := linearTwoPointRatio action first.rep second.rep first.rep_nonzero second.rep_nonzero
    first_invariant second_invariant
  have kernel_eq := linear_two_point_ratio_kernel dimension action first.rep second.rep first.rep_nonzero
    second.rep_nonzero (Projectivization.linearIndependent_pair_iff_ne.mpr distinct)
    first_invariant second_invariant
  let ratio_equiv := QuotientGroup.quotientKerEquivRange ratio
  let image_equiv := QuotientGroup.quotientKerEquivRange (projectiveLinearAction.comp action)
  let quotient_equiv : ActorType ⧸ ratio.ker ≃* ActorType ⧸ (projectiveLinearAction.comp action).ker :=
    QuotientGroup.quotientMulEquivOfEq kernel_eq
  let _finite : Finite ratio.range := Finite.of_surjective ratio.rangeRestrict ratio.rangeRestrict_surjective
  let _cyclic : IsCyclic ratio.range := isCyclic_subgroup_units ratio.range
  exact isCyclic_of_surjective ((ratio_equiv.symm.trans quotient_equiv).trans image_equiv)
    ((ratio_equiv.symm.trans quotient_equiv).trans image_equiv).surjective

end CFSG.SignalizerFunctor.Helpers
