module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

namespace CFSG
end CFSG
open CFSG

/-!
# The contragredient automorphism of `PSL₂` is inner

Dieudonne's classification of automorphisms of projective special linear
groups includes the contragredient operation `A ↦ (A⁻¹)ᵀ`.  In dimension two
this operation is conjugation by the standard symplectic matrix
`!![0, -1; 1, 0]`; hence it contributes no extra outer automorphism of
`PSL₂`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped MatrixGroups

universe u

/-- The standard symplectic matrix in `SL₂`. -/
@[expose]
public def sl2SymplecticMatrix
    (K : Type u) [CommRing K] : SL(2, K) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

set_option backward.isDefEq.respectTransparency false in
/-- In dimension two, transpose-inverse is conjugation by the standard
symplectic matrix. -/
public theorem sl2_transpose_inv_eq_conj_symplectic
    (K : Type u) [CommRing K] (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.transpose (A⁻¹) =
      sl2SymplecticMatrix K * A * (sl2SymplecticMatrix K)⁻¹ := by
  induction A using Matrix.SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sl2SymplecticMatrix,
          Matrix.SpecialLinearGroup.SL2_inv_expl,
          Matrix.mul_apply, Fin.sum_univ_two]

/-- The image in `PSL₂` of the standard symplectic matrix. -/
@[expose]
public def psl2SymplecticElement
    (K : Type u) [CommRing K] : PSL2 K :=
  QuotientGroup.mk' (Subgroup.center _) (sl2SymplecticMatrix K)

public theorem psl2SymplecticElement_eq_mk
    (K : Type u) [CommRing K] :
    psl2SymplecticElement K =
      QuotientGroup.mk' (Subgroup.center _) (sl2SymplecticMatrix K) := rfl

/-- Conjugation by the standard symplectic element acts on a projective
matrix representative by transpose-inverse. -/
public theorem psl2_conj_symplectic_mk
    (K : Type u) [CommRing K] (A : SL(2, K)) :
    MulAut.conj (psl2SymplecticElement K)
        (QuotientGroup.mk' (Subgroup.center _) A) =
      QuotientGroup.mk' (Subgroup.center _)
        (Matrix.SpecialLinearGroup.transpose (A⁻¹)) := by
  rw [MulAut.conj_apply]
  change QuotientGroup.mk' (Subgroup.center _)
      (sl2SymplecticMatrix K * A * (sl2SymplecticMatrix K)⁻¹) = _
  rw [← sl2_transpose_inv_eq_conj_symplectic]

/-- The contragredient automorphism of `PSL₂`, presented as an inner
automorphism. -/
public def psl2Contragredient
    (K : Type u) [CommRing K] : MulAut (PSL2 K) :=
  MulAut.conj (psl2SymplecticElement K)

@[simp]
public theorem psl2Contragredient_mk
    (K : Type u) [CommRing K] (A : SL(2, K)) :
    psl2Contragredient K
        (QuotientGroup.mk' (Subgroup.center _) A) =
      QuotientGroup.mk' (Subgroup.center _)
        (Matrix.SpecialLinearGroup.transpose (A⁻¹)) := by
  exact psl2_conj_symplectic_mk K A

end CFSG.GorensteinWalter
