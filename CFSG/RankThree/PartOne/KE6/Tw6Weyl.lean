module

public import CFSG.RankThree.PartOne.KE6.Phi3Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

@[expose] def tw6WWord : List (Fin 6) := [5, 4, 3, 2, 1, 3, 4, 5, 3, 4, 3, 1]

@[expose] def tw6W : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word tw6WWord)

theorem weylMatrix_tw6W : weylMatrix tw6W = -(e6T3Matrix * rhoMatrix) :=
  weylMatrix_wordProd_e6 (by decide +kernel)

theorem tw6W_smul (x : Fin Tag.E6.rank → ℤ) :
    tw6W • x = -(e6T3W • permLattice e6Rho x) := by
  rw [← weylMatrix_mulVec, weylMatrix_tw6W, permLattice_eq_mulVec, ← weylMatrix_mulVec,
    weylMatrix_e6T3W_eq, Matrix.mulVec_mulVec, Matrix.neg_mulVec]

theorem det_scalar_add_e6T3Matrix (q : ℤ) :
    (Matrix.scalar (Fin Tag.E6.rank) q + e6T3Matrix).det = (q ^ 2 - q + 1) ^ 3 := by
  have h := congrArg (Polynomial.eval (-q)) charpoly_e6T3Matrix
  rw [Matrix.eval_charpoly] at h
  have e : Matrix.scalar (Fin Tag.E6.rank) (-q) - e6T3Matrix =
      -(Matrix.scalar (Fin Tag.E6.rank) q + e6T3Matrix) := by
    rw [map_neg, neg_add', sub_eq_add_neg]
  rw [e, Matrix.det_neg, Fintype.card_fin] at h
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] at h
  have h6 : ((-1 : ℤ)) ^ Tag.E6.rank = 1 := by decide
  rw [h6, one_mul] at h
  rw [h]
  ring

end CFSG.RankThree.PartOne.KE6
