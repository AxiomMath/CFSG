module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs
import CFSG.LieType.Universal.SpinOmega.Center

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

@[expose] noncomputable def rMinusEquivStatedOmega (K : Type) [Field K] [Finite K] [CharP K 2]
    (m : ℕ) (b c : K) :
    OrthRest.RMinus K m b c ≃* StatedOmega (StatedQuadMinus (m + 1) K b c) := by
  have hbot : (LargeEvenScalars (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).subgroupOf
      (LargeEvenOmega (StatedQuadMinus (m + 1) K b c)) = ⊥ := by
    refine TableBOrth.scalars_subgroupOf_omega_eq_bot
      (Q := StatedQuadMinus (m + 1) K b c)
      (v₀ := Pi.single (Sum.inr (Sum.inr 0)) 1) (fun x v => ?_) ?_
    · rw [← CFSG.LieType.Universal.Spin.coe_quadMinus, QuadraticMap.map_smul, smul_eq_mul, sq]
    · rw [← CFSG.LieType.Universal.Spin.coe_quadMinus,
        CFSG.LieType.Universal.Spin.quadMinus_apply]
      simp
  exact (omegaMinusProjEquiv (m + 1) b c).trans (TableBOrth.projMkEquiv hbot).symm

theorem center_statedOmega_quadMinus_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center (StatedOmega (StatedQuadMinus n K b c)) = ⊥ := by
  rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadMinus hn hirr]
  refine TableBOrth.scalars_subgroupOf_omega_eq_bot (Q := StatedQuadMinus n K b c)
    (v₀ := Pi.single (Sum.inr (Sum.inr 0)) 1) (fun x v => ?_) ?_
  · rw [← CFSG.LieType.Universal.Spin.coe_quadMinus, QuadraticMap.map_smul, smul_eq_mul, sq]
  · rw [← CFSG.LieType.Universal.Spin.coe_quadMinus, CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp

end CFSG.StandardType
