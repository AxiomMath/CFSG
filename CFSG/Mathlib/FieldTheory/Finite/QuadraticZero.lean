module

public import Mathlib.FieldTheory.ChevalleyWarning

public section

namespace CFSG.FiniteField

open Matrix MvPolynomial

theorem exists_ne_zero_dotProduct_mulVec_eq_zero {K : Type*} [Field K] [Finite K]
    {σ : Type*} [Fintype σ] [DecidableEq σ] (hσ : 3 ≤ Fintype.card σ) (M : Matrix σ σ K) :
    ∃ x : σ → K, x ≠ 0 ∧ x ⬝ᵥ (M *ᵥ x) = 0 := by
  classical
  let := Fintype.ofFinite K
  let f : MvPolynomial σ K := ∑ i, ∑ j, C (M i j) * X i * X j
  have heval : ∀ v : σ → K, eval v f = v ⬝ᵥ (M *ᵥ v) := by
    intro v
    simp only [f, map_sum, map_mul, eval_C, eval_X, dotProduct, Matrix.mulVec,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdeg : f.totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro i _
    apply totalDegree_finsetSum_le
    intro j _
    have h1 := totalDegree_mul (C (M i j) * X i : MvPolynomial σ K) (X j)
    have h2 := totalDegree_mul (C (M i j) : MvPolynomial σ K) (X i)
    simp only [totalDegree_X, totalDegree_C] at h1 h2
    omega
  have hlt : f.totalDegree < Fintype.card σ := by omega
  have hdvd := char_dvd_card_solutions (ringChar K) hlt
  by_contra H
  push Not at H
  have hcard : Fintype.card {x : σ → K // eval x f = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    have h0 : eval (0 : σ → K) f = 0 := by
      rw [heval]
      simp
    refine ⟨⟨0, h0⟩, fun y => Subtype.ext ?_⟩
    obtain ⟨x, hx⟩ := y
    show x = 0
    by_contra hx0
    exact H x hx0 (by rw [← heval]; exact hx)
  rw [hcard] at hdvd
  exact CharP.ringChar_ne_one (Nat.dvd_one.1 hdvd)

end CFSG.FiniteField
