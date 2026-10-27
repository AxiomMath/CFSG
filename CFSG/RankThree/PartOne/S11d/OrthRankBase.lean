module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBasic
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Matrix Module

section Rank

variable {F E : Type*} [Field F] [Field E] {m : Type*} [Fintype m] [DecidableEq m]

theorem rank_fromBlocks_one_zero (r s : ℕ) :
    (fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)).rank = r := by
  classical
  have h : (fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0 (0 : Matrix (Fin s) (Fin s) F)) =
      diagonal (Sum.elim (fun _ : Fin r => (1 : F)) (fun _ : Fin s => (0 : F))) := by
    rw [← fromBlocks_diagonal, diagonal_one, diagonal_zero]
  rw [h, rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

theorem rank_map_eq (f : F →+* E) (M : Matrix m m F) : (M.map f).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVf : IsUnit (V.map f).det := (isUnit_iff_isUnit_det _).mp (hV.map f.mapMatrix)
  have hUf : IsUnit (U.map f).det := (isUnit_iff_isUnit_det _).mp (hU.map f.mapMatrix)
  have hE : (M.map f).rank = ((V.map f) * (M.map f) * (U.map f)).rank := by
    rw [rank_mul_eq_left_of_isUnit_det _ _ hUf, rank_mul_eq_right_of_isUnit_det _ _ hVf]
  have h1 : (V * M * U).map f = ((fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) F) 0 0
      (0 : Matrix (Fin (Fintype.card m - M.rank)) (Fin (Fintype.card m - M.rank)) F)).submatrix
        e e).map f := by rw [h]
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)] at h1
  rw [hE, h1, rank_submatrix, rank_fromBlocks_one_zero]

end Rank

section CommSpace

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}

theorem commSpace_matrixLinearEquiv {F : Type} [Field F] (A : GL (Fin d) F) :
    commSpace (matrixLinearEquiv A) = LinearMap.range (Matrix.mulVecLin (A.val - 1)) := by
  refine congrArg LinearMap.range (LinearMap.ext fun v => ?_)
  simp [matrixLinearEquiv_apply]

theorem finrank_commSpace_matrixLinearEquiv {F : Type} [Field F] (A : GL (Fin d) F) :
    finrank F (commSpace (matrixLinearEquiv A)) = (A.val - 1).rank := by
  rw [commSpace_matrixLinearEquiv]
  exact rfl

theorem finrank_commSpace_glIncl (x : GL (Fin d) k) :
    finrank K (commSpace (matrixLinearEquiv (glIncl k x))) =
      finrank k (commSpace (matrixLinearEquiv x)) := by
  rw [finrank_commSpace_matrixLinearEquiv, finrank_commSpace_matrixLinearEquiv, glIncl_val,
    ← rank_map_eq k.subtype (x.val - 1),
    Matrix.map_sub (f := ⇑k.subtype) (fun a b => map_sub k.subtype a b),
    Matrix.map_one _ (map_zero _) (map_one _)]

end CommSpace

end CFSG.RankThree.PartOne.FieldFix
