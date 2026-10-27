module

public import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type} [Field K] [Finite K]

private theorem exists_sq_eq_conjAut (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    (α : MulAut (projectiveSL n K)) : ∃ B : GL (Fin n) K, α ^ 2 = conjAut n K B := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hgen α
  obtain ⟨hmul, -, -, -, hδc, -⟩ := standard_automorphism_transport (K := K) (n := n)
  have hσ1 : fieldAut n K σ = 1 := by
    rw [ringEquiv_eq_one_of_natCard_eq_two hK σ, map_one]
  rw [hσ1, mul_one] at hαeq
  interval_cases ε
  · refine ⟨A * A, ?_⟩
    rw [hαeq, pow_zero, mul_one, sq, hmul]
  · refine ⟨A * Matrix.GeneralLinearGroup.inverseTranspose A, ?_⟩
    rw [hαeq, pow_one, sq]
    calc conjAut n K A * dualAut n K * (conjAut n K A * dualAut n K) =
          conjAut n K A * (dualAut n K * conjAut n K A * dualAut n K) := by
            simp only [mul_assoc]
      _ = conjAut n K A * conjAut n K (Matrix.GeneralLinearGroup.inverseTranspose A) := by
            rw [hδc]
      _ = conjAut n K (A * Matrix.GeneralLinearGroup.inverseTranspose A) := hmul _ _

theorem inner_of_pow_odd_eq_one (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    {α : MulAut (projectiveSL n K)} {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) :
    ∃ y : projectiveSL n K, α = MulAut.conj y := by
  obtain ⟨j, rfl⟩ := hm
  obtain ⟨B, hB⟩ := exists_sq_eq_conjAut hK hn α
  have hαB : α = (α ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, hα, one_mul]
  rw [hB, ← map_pow] at hαB
  obtain ⟨y, hy⟩ := conjAut_mem_range_conj_of_det_eq_pow (A := B ^ (j + 1)) (μ := 1)
    (by rw [det_eq_one_of_natCard_eq_two hK, one_pow])
  exact ⟨y, hαB.trans hy.symm⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214
