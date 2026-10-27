module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RepresentationTheory.Irreducible
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtendScalars
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.JacobsonDensity
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

namespace CFSG
end CFSG
open CFSG

open scoped TensorProduct
open scoped MonoidAlgebra

namespace CFSG.Theory.Representation

open _root_.Representation

section AbsolutelyIrreducibleRep

variable {F G V W : Type*} [Monoid G] [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] (ρ : Representation F G V) (σ : Representation F G W)

/-- A representation is absolutely irreducible if it remains irreducible after extending scalars
to an algebraic closure of the base field. -/
@[mk_iff]
public class IsAbsolutelyIrreducible: Prop where
  irreducible_of_closure : IsIrreducible (extendScalars (AlgebraicClosure F) ρ)

set_option backward.isDefEq.respectTransparency false in
public theorem isAbsolutelyIrreducible_iff_surjective [FiniteDimensional F V] [IsIrreducible ρ] :
    IsAbsolutelyIrreducible ρ ↔ Function.Surjective (algebraMap F (End ρ)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · let : (extendScalars (AlgebraicClosure F) ρ).IsIrreducible :=
      (isAbsolutelyIrreducible_iff ρ).mp h
    have := jacobson_density_surjective_isAlgClosed_rep (extendScalars (AlgebraicClosure F) ρ)
    rw [← extendScalars_surj_iff] at this
    exact surjective_of_jacobson_density_surjective_rep ρ this
  · let : Nontrivial (AlgebraicClosure F ⊗[F] V) := by
      rw [Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right]
      exact Subrepresentation.irreducible_module_nontrivial ρ
    apply irreducible_of_jacobson_density_surjective
    rw [← extendScalars_surj_iff]
    exact jacobson_density_surjective_rep ρ h

public theorem IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible [inst : IsAbsolutelyIrreducible ρ] : IsIrreducible ρ :=
  irreducible_of_extendScalars (AlgebraicClosure F) ρ (inst := inst.irreducible_of_closure)

set_option backward.isDefEq.respectTransparency false in
public theorem IsAbsolutelyIrreducible.irreducible_of_extension [FiniteDimensional F V]  (F' : Type*) [Field F'] [Algebra F F'] [inst : IsAbsolutelyIrreducible ρ] : IsIrreducible (extendScalars F' ρ) := by
  let : (extendScalars (AlgebraicClosure F) ρ).IsIrreducible := inst.irreducible_of_closure
  let : IsIrreducible ρ := irreducible_of_isAbsolutelyIrreducible ρ
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine irreducible_of_jacobson_density_surjective (extendScalars F' ρ) ?_
  rw [← extendScalars_surj_iff F' ρ, extendScalars_surj_iff (AlgebraicClosure F) ρ]
  exact jacobson_density_surjective_isAlgClosed_rep (extendScalars (AlgebraicClosure F) ρ)

set_option backward.isDefEq.respectTransparency false in
public theorem IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_extendScalars [FiniteDimensional F V]  (F' : Type*) [Field F'] [Algebra F F'] :
    IsAbsolutelyIrreducible (extendScalars F' ρ) ↔ IsAbsolutelyIrreducible ρ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [isAbsolutelyIrreducible_iff] at ⊢ h
    rw [RepEquiv.irreducible_euqiv (extendScalars_comp _)] at h
    let : Nontrivial V := by
      have : Nontrivial (AlgebraicClosure F' ⊗[F] V) := Subrepresentation.irreducible_module_nontrivial (extendScalars (AlgebraicClosure F') ρ)
      contrapose! this
      exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right F (AlgebraicClosure F')).mpr this
    apply irreducible_of_jacobson_density_surjective
    rw [← extendScalars_surj_iff]
    have : Algebra.adjoin (AlgebraicClosure F') (Set.range (extendScalars (AlgebraicClosure F') ρ)) = ⊤ := jacobson_density_surjective_isAlgClosed_rep _
    rw [← extendScalars_surj_iff (F := F) (F' := (AlgebraicClosure F'))] at this
    exact this
  · rw [isAbsolutelyIrreducible_iff] at ⊢ h
    rw [RepEquiv.irreducible_euqiv (extendScalars_comp _)]
    let : Nontrivial V := by
      have : Nontrivial (AlgebraicClosure F ⊗[F] V) := Subrepresentation.irreducible_module_nontrivial (extendScalars (AlgebraicClosure F) ρ)
      contrapose! this
      exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right F (AlgebraicClosure F)).mpr this
    apply irreducible_of_jacobson_density_surjective
    rw [← extendScalars_surj_iff]
    have : Algebra.adjoin (AlgebraicClosure F) (Set.range (extendScalars (AlgebraicClosure F) ρ)) = ⊤ := jacobson_density_surjective_isAlgClosed_rep _
    rw [← extendScalars_surj_iff (F := F) (F' := (AlgebraicClosure F))] at this
    exact this

variable {ρ} {σ}


end AbsolutelyIrreducibleRep

end CFSG.Theory.Representation
