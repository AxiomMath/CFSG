module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.StandardType.LinearFieldFix

open CFSG.Assembly

variable {d : ℕ}

theorem isSimpleGroup_proj (hd : 3 ≤ d) (F : Type) [Field F] :
    IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) := by
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin d) F) :=
    (CFSG.LinearGroups.linear_projective_simple (K := F) (n := d) (by omega)
      (Or.inl hd)).2.1
  exact MulEquiv.isSimpleGroup
    ((TypeA.recipeEquiv d F).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        d F).symm)

theorem exists_noncomm_proj (hd : 3 ≤ d) (F : Type) [Field F] :
    ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin d) F), a * b ≠ b * a := by
  let e : LargeEvenProj (LargeEvenSLGroup (Fin d) F) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin d) F :=
    (TypeA.recipeEquiv d F).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        d F).symm
  haveI : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin d) F) :=
    CFSG.LinearGroups.linear_projective_perfect (K := F) (n := d) (by omega) (Or.inl hd)
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Nontrivial (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) :=
    (isSimpleGroup_proj hd F).toNontrivial
  by_contra h
  push_neg at h
  haveI : IsMulCommutative (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) :=
    IsMulCommutative.of_comm h
  exact Group.IsPerfect.not_isMulCommutative (LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    inferInstance

end CFSG.StandardType.LinearFieldFix

end
