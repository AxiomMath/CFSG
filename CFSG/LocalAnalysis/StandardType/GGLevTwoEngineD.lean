module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots
import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxCase

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin LevTwoType

private theorem levTwoS2d_engine_cartanD (n : ℕ) (hn : 4 ≤ n) : LevTwoEngine (LevTwoType.D n) :=
  levTwoS2d_engine_of_eq (levTwoS2d_root_eq n).symm (isFiniteType_cartanD n)
    (LevTwoType.rootFT (LevTwoType.D n))
    (fun p hp hp2 c Φ hΦ => by
      have : Fact p.Prime := ⟨hp⟩
      exact levTwoS2d_tcRoot n hn hp2 c hΦ)

theorem levTwoEngine_D (n : ℕ) (hn : 4 ≤ n) : LevTwoEngine (LevTwoType.D n) :=
  levTwoS2d_engine_cartanD n hn

end CFSG.StandardType.LevTwo
