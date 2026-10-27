module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoStd
public import Mathlib.LinearAlgebra.Matrix.Rank
import CFSG.LocalAnalysis.StandardType.GGLevTwoS4cAux

public section

namespace CFSG.StandardType.LevTwo

open LevTwoType

theorem levTwoRankPairModP (T : LevTwoType) (hT : T.Valid) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    T.n ≤ Matrix.rank (T.pair.map (Int.castRingHom (ZMod p))) + 1 ∧
      (¬ (p : ℤ) ∣ T.pair.det → Matrix.rank (T.pair.map (Int.castRingHom (ZMod p))) = T.n) :=
  levTwoS4c_rankPair T hT p hp hp2

end CFSG.StandardType.LevTwo
