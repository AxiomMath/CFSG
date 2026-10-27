module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEndMat
public import CFSG.RankThree.PartOne.AUTSL.OmegaModel

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615

theorem orthCenter_trivial {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 8 ≤ n)
    (Phi : QuadraticForm K (Fin n → K)) (hnd : (QuadraticMap.polarBilin Phi).Nondegenerate)
    (z : ↥(StatedOmega ⇑Phi)) (hz : ∀ h : ↥(StatedOmega ⇑Phi), z * h = h * z) : z = 1 := by
  have hcenter : Subgroup.center (StatedOmega ⇑Phi) = ⊥ := by
    rw [← CFSG.RankThree.PartOne.AUTSL.matrixDerived_eq_statedOmega Phi]
    exact CFSG.StandardType.OrthRestOdd.center_matrixDerived_eq_bot hnd hn
  have hzmem : z ∈ Subgroup.center (StatedOmega ⇑Phi) := by
    rw [Subgroup.mem_center_iff]
    intro h
    exact (hz h).symm
  rw [hcenter] at hzmem
  simpa using hzmem

end S2MathAs3_1619Final

end
