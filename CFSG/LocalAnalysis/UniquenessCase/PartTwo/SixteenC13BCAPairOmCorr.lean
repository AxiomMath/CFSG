module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

private theorem s16c13bcA_Q_add_smul {ι K : Type} [Fintype ι] [Field K]
    {Q : (ι → K) → K} {M : Matrix ι ι K}
    (h : IsQuadWith Q M) {a w : ι → K} (hQw : Q w = 0) (haw : a ⬝ᵥ (M *ᵥ w) = 0) (μ : K) :
    Q (a + μ • w) = Q a := by
  rw [h.add, h.smul, hQw, Matrix.mulVec_smul, dotProduct_smul, haw, smul_eq_mul]
  ring

private theorem s16c13bcA_dot_add_smul {ι K : Type} [Fintype ι] [Field K]
    {M : Matrix ι ι K} {a b w : ι → K}
    (hww : w ⬝ᵥ (M *ᵥ w) = 0) (μ μ' : K) :
    (a + μ • w) ⬝ᵥ (M *ᵥ (b + μ' • w)) =
      a ⬝ᵥ (M *ᵥ b) + μ' * (a ⬝ᵥ (M *ᵥ w)) + μ * (w ⬝ᵥ (M *ᵥ b)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, hww]
  ring

private theorem s16c13bcA_dot_add_smul_eq {ι K : Type} [Fintype ι] [Field K]
    {M : Matrix ι ι K} {a b w : ι → K}
    (hww : w ⬝ᵥ (M *ᵥ w) = 0) (haw : a ⬝ᵥ (M *ᵥ w) = 0) (hwb : w ⬝ᵥ (M *ᵥ b) = 0)
    (μ μ' : K) : (a + μ • w) ⬝ᵥ (M *ᵥ (b + μ' • w)) = a ⬝ᵥ (M *ᵥ b) := by
  rw [s16c13bcA_dot_add_smul hww, haw, hwb, mul_zero, mul_zero, add_zero, add_zero]

private theorem s16c13bcA_v_add_smul {ι K : Type} [Fintype ι] [Field K] [CharP K 2]
    {M : Matrix ι ι K} {a w v : ι → K}
    (hvw : v ⬝ᵥ (M *ᵥ w) ≠ 0) :
    v ⬝ᵥ (M *ᵥ (a + (v ⬝ᵥ (M *ᵥ a) / (v ⬝ᵥ (M *ᵥ w))) • w)) = 0 := by
  have hμ : (v ⬝ᵥ (M *ᵥ a) / (v ⬝ᵥ (M *ᵥ w))) * (v ⬝ᵥ (M *ᵥ w)) = v ⬝ᵥ (M *ᵥ a) :=
    div_mul_cancel₀ _ hvw
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  linear_combination (v ⬝ᵥ (M *ᵥ a)) * two_eq_zero_K (K := K) + hμ

theorem s16c13bcA_pairs_of_singular {ι K : Type} [Fintype ι] [Field K] [CharP K 2]
    {Q : (ι → K) → K} {M : Matrix ι ι K} (h : IsQuadWith Q M) {a₁ a₁' a₂ a₂' w v : ι → K}
    (h1 : Q a₁ = 1) (h1' : Q a₁' = 1) (h11 : a₁ ⬝ᵥ (M *ᵥ a₁') = 1)
    (h2 : Q a₂ = 1) (h2' : Q a₂' = 1) (h22 : a₂ ⬝ᵥ (M *ᵥ a₂') = 1)
    (h12 : a₁ ⬝ᵥ (M *ᵥ a₂) = 0) (h12' : a₁ ⬝ᵥ (M *ᵥ a₂') = 0)
    (h1'2 : a₁' ⬝ᵥ (M *ᵥ a₂) = 0) (h1'2' : a₁' ⬝ᵥ (M *ᵥ a₂') = 0)
    (hwQ : Q w = 0) (hw1 : w ⬝ᵥ (M *ᵥ a₁) = 0) (hw1' : w ⬝ᵥ (M *ᵥ a₁') = 0)
    (hw2 : w ⬝ᵥ (M *ᵥ a₂) = 0) (hw2' : w ⬝ᵥ (M *ᵥ a₂') = 0)
    (hvw : v ⬝ᵥ (M *ᵥ w) ≠ 0) :
    ∃ b₁ b₁' b₂ b₂' : ι → K,
      Q b₁ = 1 ∧ Q b₁' = 1 ∧ b₁ ⬝ᵥ (M *ᵥ b₁') = 1 ∧
      Q b₂ = 1 ∧ Q b₂' = 1 ∧ b₂ ⬝ᵥ (M *ᵥ b₂') = 1 ∧
      b₁ ⬝ᵥ (M *ᵥ b₂) = 0 ∧ b₁ ⬝ᵥ (M *ᵥ b₂') = 0 ∧
      b₁' ⬝ᵥ (M *ᵥ b₂) = 0 ∧ b₁' ⬝ᵥ (M *ᵥ b₂') = 0 ∧
      v ⬝ᵥ (M *ᵥ b₁) = 0 ∧ v ⬝ᵥ (M *ᵥ b₁') = 0 ∧ v ⬝ᵥ (M *ᵥ b₂) = 0 ∧ v ⬝ᵥ (M *ᵥ b₂') = 0 := by
  have hww : w ⬝ᵥ (M *ᵥ w) = 0 := h.self w
  have hw1'' : a₁ ⬝ᵥ (M *ᵥ w) = 0 := (h.symm a₁ w).trans hw1
  have hw1''' : a₁' ⬝ᵥ (M *ᵥ w) = 0 := (h.symm a₁' w).trans hw1'
  have hw2'' : a₂ ⬝ᵥ (M *ᵥ w) = 0 := (h.symm a₂ w).trans hw2
  have hw2''' : a₂' ⬝ᵥ (M *ᵥ w) = 0 := (h.symm a₂' w).trans hw2'
  refine ⟨a₁ + (v ⬝ᵥ (M *ᵥ a₁) / (v ⬝ᵥ (M *ᵥ w))) • w,
    a₁' + (v ⬝ᵥ (M *ᵥ a₁') / (v ⬝ᵥ (M *ᵥ w))) • w,
    a₂ + (v ⬝ᵥ (M *ᵥ a₂) / (v ⬝ᵥ (M *ᵥ w))) • w,
    a₂' + (v ⬝ᵥ (M *ᵥ a₂') / (v ⬝ᵥ (M *ᵥ w))) • w,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s16c13bcA_Q_add_smul h hwQ hw1'', h1]
  · rw [s16c13bcA_Q_add_smul h hwQ hw1''', h1']
  · rw [s16c13bcA_dot_add_smul_eq hww hw1'' hw1', h11]
  · rw [s16c13bcA_Q_add_smul h hwQ hw2'', h2]
  · rw [s16c13bcA_Q_add_smul h hwQ hw2''', h2']
  · rw [s16c13bcA_dot_add_smul_eq hww hw2'' hw2', h22]
  · rw [s16c13bcA_dot_add_smul_eq hww hw1'' hw2, h12]
  · rw [s16c13bcA_dot_add_smul_eq hww hw1'' hw2', h12']
  · rw [s16c13bcA_dot_add_smul_eq hww hw1''' hw2, h1'2]
  · rw [s16c13bcA_dot_add_smul_eq hww hw1''' hw2', h1'2']
  · exact s16c13bcA_v_add_smul hvw
  · exact s16c13bcA_v_add_smul hvw
  · exact s16c13bcA_v_add_smul hvw
  · exact s16c13bcA_v_add_smul hvw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
