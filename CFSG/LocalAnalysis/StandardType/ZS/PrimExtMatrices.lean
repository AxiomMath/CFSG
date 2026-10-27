module

public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
public import TauCeti.LinearAlgebra.Matrix.BlockSucc

public section

namespace CFSG.StandardType.ZS

section Matrices

variable {K : Type} [Field K]

@[expose] def h3BlockMat (α : K) : Matrix (Fin 3) (Fin 3) K :=
  (2 : K)⁻¹ • Matrix.of ![![α, 1, 2 - α], ![1, 1 - α, -1], ![1, -(1 + α), 1]]

@[expose] def h3BlockMats (α : K) : Set (Matrix (Fin 3) (Fin 3) K) :=
  {diagSignMat 0, diagSignMat 1, diagSignMat 2, h3BlockMat α}

@[expose] def h3Mats (α : K) : Set (Matrix (Fin 4) (Fin 4) K) :=
  Matrix.blockSucc '' h3BlockMats α

@[expose] def h4BlockMat (α : K) : Matrix (Fin 4) (Fin 4) K :=
  (2 : K)⁻¹ • Matrix.of
    ![![2, 0, 0, 0], ![0, α, 2 - α, -1], ![0, 1, 1, 1 + α], ![0, -1, 1, 1 - α]]

@[expose] def h4BlockMats (α : K) : Set (Matrix (Fin 4) (Fin 4) K) :=
  insert (h4BlockMat α) (h3Mats α)

@[expose] def h4Mats (α : K) : Set (Matrix (Fin 5) (Fin 5) K) :=
  Matrix.blockSucc '' h4BlockMats α

@[expose] def j34BlockMat (β : K) : Matrix (Fin 3) (Fin 3) K :=
  (2 : K)⁻¹ • Matrix.of ![![1, β⁻¹, 1], ![2 * β, 0, -(2 * β)], ![1, -β⁻¹, 1]]

@[expose] def j34BlockMats (β : K) : Set (Matrix (Fin 3) (Fin 3) K) :=
  {diagSignMat 0, pijMat 0 1 1, pijMat 1 2 1, j34BlockMat β}

@[expose] def j34Mats (β : K) : Set (Matrix (Fin 4) (Fin 4) K) :=
  Matrix.blockSucc '' j34BlockMats β

@[expose] def f4ExtMats : Set (Matrix (Fin 5) (Fin 5) K) :=
  Matrix.blockSucc '' weylF4Mats

@[expose] def h4CandRoot (α : K) (k : Fin 3) : Fin 4 → K :=
  ![![0, 1, -(1 + α), 1 + α], ![0, 1, 1 - α, α - 1], ![0, 1, -(1 + α), α - 1]] k

@[expose] def h4CandCoroot (α : K) (k : Fin 3) : Fin 4 → K :=
  ![![0, 1 - α / 2, α / 2 - 1, 1 / 2], ![0, (1 + α) / 2, (1 - α) / 2, α / 2],
    ![0, 1 / 2, -(1 / 2), (α - 1) / 2]] k

@[expose] def h4CandMat (α : K) (k : Fin 3) : Matrix (Fin 4) (Fin 4) K :=
  1 - Matrix.vecMulVec (h4CandRoot α k) (h4CandCoroot α k)

end Matrices

end CFSG.StandardType.ZS

end
