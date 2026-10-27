module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDADefs
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDAOrthCore
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDARefute
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem ggInnerOrUnitaryOnComps_omegaPlus {K : Type} [Field K] [Finite K] {g m : ℕ}
    (hK : Nat.card K = 2 ^ g) (hg : 3 ∣ 2 ^ g + 1) (hm : 4 ≤ m) :
    GGInnerOrUnitaryOnComps (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) := by
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := m)
    (by omega)
  exact ggInnerOrUnitaryOnComps_of_mulEquiv
    (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.projOrthEquiv
      (CFSG.LieType.Universal.Spin.coe_quadPlus (n := m) (K := K))).symm
    (ggInnerOrUnitaryOnComps_projOrthDerived hQ hT hK hg)

theorem ggInnerOrUnitaryOnComps_omegaMinus {K : Type} [Field K] [Finite K] {g m : ℕ}
    (hK : Nat.card K = 2 ^ g) (hg : 3 ∣ 2 ^ g + 1) (hm : 3 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGInnerOrUnitaryOnComps (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) := by
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := m + 1)
    (by omega) hbc
  have e : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) K b c)) :=
    (CFSG.Open.StatedAPI.mapMkEquivStatedProj (LargeEvenOmega (LargeEvenQMinus m b c))).symm.trans
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.omegaModelEquivOfReindex
        (Equiv.sumAssoc (Fin m) (Fin m) (Fin 2)) (Q := LargeEvenQMinus m b c)
        (Q' := CFSG.Open.StatedQuadMinus (m + 1) K b c) fun _ => rfl)
  exact ggInnerOrUnitaryOnComps_of_mulEquiv
    (e.trans (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.projOrthEquiv
      (CFSG.LieType.Universal.Spin.coe_quadMinus (m + 1) K b c))).symm
    (ggInnerOrUnitaryOnComps_projOrthDerived hQ hT hK hg)

end CFSG.StandardType.SCFourCover

end
