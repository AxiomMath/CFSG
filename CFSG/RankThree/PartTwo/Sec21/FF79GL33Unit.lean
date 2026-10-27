module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Code

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

section Basis

variable (v w₁ w₂ : Vec)

@[expose] def basisMat : Mat := Matrix.of ![v, w₁, w₂]

theorem isUnit_basisMat (hli : LinearIndependent (ZMod 3) ![v, w₁, w₂]) :
    IsUnit (basisMat v w₁ w₂) := by
  refine (Matrix.linearIndependent_rows_iff_isUnit (K := ZMod 3)
    (A := basisMat v w₁ w₂)).mp ?_
  exact hli

theorem li_vecMul (P : GL (Fin 3) (ZMod 3)) (hli : LinearIndependent (ZMod 3) ![v, w₁, w₂]) :
    LinearIndependent (ZMod 3)
      ![Matrix.vecMul v (P : Mat), Matrix.vecMul w₁ (P : Mat), Matrix.vecMul w₂ (P : Mat)] := by
  have hu : IsUnit (basisMat (Matrix.vecMul v (P : Mat)) (Matrix.vecMul w₁ (P : Mat))
      (Matrix.vecMul w₂ (P : Mat))) := by
    have : basisMat (Matrix.vecMul v (P : Mat)) (Matrix.vecMul w₁ (P : Mat))
        (Matrix.vecMul w₂ (P : Mat)) = basisMat v w₁ w₂ * (P : Mat) := by
      ext i j
      fin_cases i <;> simp [basisMat, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [this]
    exact (isUnit_basisMat v w₁ w₂ hli).mul P.isUnit
  exact (Matrix.linearIndependent_rows_iff_isUnit (K := ZMod 3)
    (A := basisMat (Matrix.vecMul v (P : Mat)) (Matrix.vecMul w₁ (P : Mat))
      (Matrix.vecMul w₂ (P : Mat)))).mpr hu

end Basis

end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end
