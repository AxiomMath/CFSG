module

public import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private lemma s1614_lp_lowerTriangular (K : Type) [Field K] (d : Fin 4 → K) :
    (Matrix.of (fun i k : Fin 4 =>
      if i = 3 then d k else if i = k then 1 else 0)).IsLowerTriangular := by
  intro i k hik
  have hlt : i < k := hik
  simp only [Matrix.of_apply]
  split_ifs with h3 hik'
  · exfalso; omega
  · exact absurd hik' (ne_of_lt hlt)
  · rfl

private lemma s1614_lp_det (K : Type) [Field K] (d : Fin 4 → K) :
    (Matrix.of (fun i k : Fin 4 =>
      if i = 3 then d k else if i = k then 1 else 0)).det = d 3 := by
  rw [Matrix.det_of_isLowerTriangular _ (s1614_lp_lowerTriangular K d), Fin.prod_univ_four]
  simp [Matrix.of_apply]

theorem s1614_ln_pivot (K : Type) [Field K] {c : Fin 4 → K} (hc : c ≠ 0) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 4) K,
      ∀ v : Fin 4 → K,
        (((P : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v) 3 =
          dotProduct c v := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  rw [Pi.zero_apply] at hj
  set σ : Equiv.Perm (Fin 4) := Equiv.swap j 3 with hσ
  set Q : Matrix (Fin 4) (Fin 4) K :=
    Matrix.of fun i k => if i = 3 then c (σ k) else if i = k then 1 else 0 with hQ
  set Pm : Matrix (Fin 4) (Fin 4) K := σ.permMatrix K with hPm
  have hσ3 : σ 3 = j := by
    rw [hσ]; exact Equiv.swap_apply_right j 3
  have hQdet : Q.det ≠ 0 := by
    have h : Q.det = c j := by rw [hQ, s1614_lp_det K (fun k => c (σ k)), hσ3]
    rw [h]; exact hj
  have hPmdet : Pm.det ≠ 0 := by
    rw [hPm, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  have hPdet : (Q * Pm).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero hQdet hPmdet
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Q * Pm) hPdet, ?_⟩
  intro v
  show ((Q * Pm).mulVec v) 3 = dotProduct c v
  rw [← Matrix.mulVec_mulVec]
  have hPmv : Pm.mulVec v = v ∘ σ := by
    rw [hPm]
    exact Matrix.permMatrix_mulVec (R := K) (σ := σ)
  rw [hPmv]
  change (Q.mulVec (v ∘ σ)) 3 = dotProduct c v
  rw [hQ, Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.of_apply, Function.comp_apply, dotProduct, if_true]
  exact Equiv.sum_comp σ (fun i => c i * v i)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
