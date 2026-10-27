module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticLagrangian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6B3

open Matrix CFSG.Open
open CFSG.SeitzReduction CFSG.SeitzReduction.SymplecticLagrangian
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open SymplecticFlag SymplecticHigher SymplecticTorusWeyl

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem displacement_eq_orthogonal_of_rank_three {y : StatedSp 3 K} (hy : y * y = 1)
    (hrk : (((y : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) - 1).rank = 3) :
    displacement y = (pairedSympForm K 3).orthogonal (displacement y) := by
  have hdim : Module.finrank K (displacement y) = 3 := by
    change Module.finrank K (LinearMap.range (spMat y - 1).mulVecLin) = 3
    rw [Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols]
    exact hrk
  have hle : displacement y ≤ (pairedSympForm K 3).orthogonal (displacement y) := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    exact isTotallyIsotropic_displacement hy z hz x hx
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.BilinForm.finrank_orthogonal SymplecticFlag.pairedSympForm_nondegenerate,
    finrank_standard, hdim]

omit [Finite K] in
theorem not_forall_dotProduct_eq_zero_of_symmetric_three {S : Matrix (Fin 3) (Fin 3) K}
    (hS : Sᵀ = S) (hSu : IsUnit S) : ¬∀ x : Fin 3 → K, x ⬝ᵥ (S *ᵥ x) = 0 := by
  intro halt
  have hdiag : ∀ i : Fin 3, S i i = 0 := by
    intro i
    simpa [Matrix.mulVec_single_one, dotProduct_comm, dotProduct_single_one] using
      halt (Pi.single i 1)
  have hsym : ∀ i j : Fin 3, S j i = S i j := fun i j =>
    congrFun (congrFun hS i) j
  have hdet : S.det = 0 := by
    rw [Matrix.det_fin_three]
    simp only [hdiag, zero_mul, mul_zero, sub_zero, zero_add]
    rw [hsym 0 2, hsym 1 2, hsym 0 1]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (S 0 1 * S 1 2 * S 0 2) * h2
  exact ((Matrix.isUnit_iff_isUnit_det S).mp hSu).ne_zero hdet

theorem exists_eq_conj_upperUnipotent_one_of_rank_three {y : StatedSp 3 K}
    (hy : y * y = 1)
    (hrk : (((y : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) - 1).rank = 3) :
    ∃ g : StatedSp 3 K,
      y = g * upperUnipotentSp 3 K (transpose_one : (1 : Matrix (Fin 3) (Fin 3) K)ᵀ = 1) * g⁻¹ := by
  obtain ⟨g, S, hS, hSu, hyS⟩ := exists_eq_conj_upperUnipotentSp hy
    (displacement_eq_orthogonal_of_rank_three hy hrk)
  obtain ⟨P, hP⟩ := exists_mul_mul_transpose_eq_one hS hSu
    (not_forall_dotProduct_eq_zero_of_symmetric_three hS hSu)
  have hconj : leviSp P * upperUnipotentSp 3 K hS * (leviSp P)⁻¹ =
      upperUnipotentSp 3 K (transpose_one : (1 : Matrix (Fin 3) (Fin 3) K)ᵀ = 1) := by
    rw [leviSp_conj_upperUnipotentSp]
    exact upperUnipotentSp_eq_of_eq _ _ hP
  refine ⟨g * (leviSp P)⁻¹, ?_⟩
  rw [hyS, ← hconj]
  group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6B3
