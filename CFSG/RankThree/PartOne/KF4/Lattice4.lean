module

public import CFSG.RankThree.PartOne.KF4.Lattice3

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open scoped Matrix

@[expose] def f4W4 : WeylGroup Tag.F4 :=
  (coxeterSystem Tag.F4).wordProd [f4Index 0, f4Index 1, f4Index 2, f4Index 3] ^ 3

@[expose] def f4W4Mat : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![1, 0, 0, -1; 2, 1, -1, -1; 2, 2, -1, -2; 2, 0, 0, -1]

theorem f4W4Mat_sq : f4W4Mat * f4W4Mat = -1 := by decide +kernel

theorem f4W4_eq_wordProd : f4W4 = (coxeterSystem Tag.F4).wordProd
    ([f4Index 0, f4Index 1, f4Index 2, f4Index 3] ++ [f4Index 0, f4Index 1, f4Index 2, f4Index 3] ++
      [f4Index 0, f4Index 1, f4Index 2, f4Index 3]) := by
  simp only [f4W4, pow_succ, pow_zero, one_mul, CoxeterSystem.wordProd_append]

theorem weylMatrix_f4W4 : weylMatrix f4W4 = f4W4Mat := by
  rw [f4W4_eq_wordProd]
  exact weylMatrix_wordProd_of' (by decide +kernel)

theorem f4W4_smul (x : Fin Tag.F4.rank → ℤ) : f4W4 • x = f4W4Mat *ᵥ x := by
  rw [← weylMatrix_mulVec, weylMatrix_f4W4]

theorem f4W4_smul_smul (x : Fin Tag.F4.rank → ℤ) : f4W4 • f4W4 • x = -x := by
  rw [f4W4_smul, f4W4_smul, Matrix.mulVec_mulVec, f4W4Mat_sq, Matrix.neg_mulVec,
    Matrix.one_mulVec]

end CFSG.RankThree.PartOne.KF4
