module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.StandardType.ZS

theorem owPo_polar_weightedSumSquares {K : Type*} [CommRing K] {d : ℕ}
    (w : Fin d → K) (x y : Fin d → K) :
    QuadraticMap.polar (QuadraticMap.weightedSumSquares K w) x y =
      2 * ∑ i, w i * (x i * y i) := by
  simp only [QuadraticMap.polar, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
    Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end CFSG.StandardType.ZS

end
