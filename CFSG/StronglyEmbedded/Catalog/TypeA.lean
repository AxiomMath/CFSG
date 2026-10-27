module

public import CFSG.StronglyEmbedded.Catalog.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

public section

namespace CFSG.BenderSuzuki.Catalog

open TauCeti

variable (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)

instance charP_closure_A : CharP (ValidLieTypeIndex.Closure ⟨_, hv⟩) q.p := by
  have h := (inferInstance : CharP (ValidLieTypeIndex.Closure ⟨_, hv⟩)
    (ValidLieTypeIndex.characteristic ⟨_, hv⟩))
  simpa only [ValidLieTypeIndex.characteristic, LieTypeIndex.characteristic_A] using h

noncomputable def carrierEquivA :
    ValidLieTypeIndex.AmbientGroup ⟨_, hv⟩ ≃* (TypeALieIndex.ofA r q hv).StandardGroup :=
  (TypeALieIndex.ofA r q hv).carrierEquivSpecialLinear

private theorem carrierEquiv_comp_steinberg [Fact q.p.Prime] :
    (carrierEquivA r q hv).toMonoidHom.comp
      (ValidLieTypeIndex.steinberg ⟨_, hv⟩) =
    (slFrobenius (p := q.p) (ValidLieTypeIndex.Closure ⟨_, hv⟩) q.exponent).comp
      (carrierEquivA r q hv).toMonoidHom := by
  refine MonoidHom.ext fun g => Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have key := (TypeALieIndex.ofA r q hv).carrierEquivSpecialLinear_steinberg g
  rw [TypeALieIndex.specialLinearSteinberg, TypeALieIndex.specialLinearGraphAut_ofA] at key
  refine (congrArg (fun x : (TypeALieIndex.ofA r q hv).StandardGroup => x.1 i j) key).trans ?_
  simp [TypeALieIndex.specialLinearFrobenius, iterateFrobenius_def, carrierEquivA,
    ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent]
  rfl

noncomputable def groupEquivPSL
    [Fact q.p.Prime]
    [IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent))]
    (hP : ¬ IsMulCommutative
      (Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent))) :
    ValidLieTypeIndex.Group ⟨_, hv⟩ ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent) :=
  (FixedPointCandidate.congr _ (carrierEquiv_comp_steinberg r q hv)).trans
    (fixedPointCandidateEquivPSL (m := Fin (r + 1)) q.exponent_pos.ne' hP)

end CFSG.BenderSuzuki.Catalog
