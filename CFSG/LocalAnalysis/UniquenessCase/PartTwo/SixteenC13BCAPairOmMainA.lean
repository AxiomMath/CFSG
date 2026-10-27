module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {K : Type} [Field K] {n : ℕ}

@[expose] def s16c13bcA_minusD (n : ℕ) (K : Type) [Field K] (j k : Fin (n - 1)) :
    Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
  Pi.single (.inl j) 1 + Pi.single (.inr (.inl j)) 1 + Pi.single (.inl k) 1

private theorem s16c13bcA_minusM_mulVec_inl (b : K)
    (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (i : Fin (n - 1)) :
    (minusM n K b *ᵥ y) (.inl i) = y (.inr (.inl i)) := by
  simpa [minusEmb] using minusM_mulVec_emb b y (Sum.inr i)

private theorem s16c13bcA_minusM_mulVec_inr (b : K)
    (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (i : Fin (n - 1)) :
    (minusM n K b *ᵥ y) (.inr (.inl i)) = y (.inl i) := by
  simpa [minusEmb] using minusM_mulVec_emb b y (Sum.inl i)

private theorem s16c13bcA_dot_single_inl (b : K)
    (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (i : Fin (n - 1)) :
    (Pi.single (.inl i) 1 : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ⬝ᵥ (minusM n K b *ᵥ y) =
      y (.inr (.inl i)) := by
  rw [single_dotProduct, one_mul, s16c13bcA_minusM_mulVec_inl]

private theorem s16c13bcA_dot_single_inr (b : K)
    (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (i : Fin (n - 1)) :
    (Pi.single (.inr (.inl i)) 1 : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ⬝ᵥ
        (minusM n K b *ᵥ y) = y (.inl i) := by
  rw [single_dotProduct, one_mul, s16c13bcA_minusM_mulVec_inr]

private theorem s16c13bcA_dot_single_u (b : K)
    (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    (Pi.single (.inr (.inr 0)) 1 : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ⬝ᵥ
        (minusM n K b *ᵥ y) = b * y (.inr (.inr 1)) := by
  rw [single_dotProduct, one_mul, minusM_mulVec_zero]

private theorem s16c13bcA_dot_single_t (b : K)
    (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    (Pi.single (.inr (.inr 1)) 1 : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ⬝ᵥ
        (minusM n K b *ᵥ y) = b * y (.inr (.inr 0)) := by
  rw [single_dotProduct, one_mul, minusM_mulVec_one]

theorem s16c13bcA_Q_minusD (b c : K) {j k : Fin (n - 1)} (hjk : j ≠ k) :
    CFSG.Open.StatedQuadMinus n K b c (s16c13bcA_minusD n K j k) = 1 := by
  simp [CFSG.Open.StatedQuadMinus, s16c13bcA_minusD, Pi.single_apply, hjk, hjk.symm]

theorem s16c13bcA_B_minusD (b : K) {j k : Fin (n - 1)} (hjk : j ≠ k) :
    minusA n K k ⬝ᵥ (minusM n K b *ᵥ s16c13bcA_minusD n K j k) = 1 := by
  simp only [minusA, s16c13bcA_minusD]
  simp only [dotProduct_add, add_dotProduct, Matrix.mulVec_add, s16c13bcA_dot_single_inl,
    s16c13bcA_dot_single_inr, s16c13bcA_dot_single_u, s16c13bcA_dot_single_t,
    Pi.single_apply]
  simp [hjk, hjk.symm]

theorem s16c13bcA_minusD_apply_eq_zero {j k : Fin (n - 1)}
    {r : Fin (n - 1) ⊕ Fin (n - 1)} (hj : minusIdx r ≠ j) (hk : minusIdx r ≠ k) :
    (s16c13bcA_minusD n K j k) (minusEmb n r) = 0 := by
  rcases r with c | c <;> simp_all [minusIdx, minusEmb, s16c13bcA_minusD]

theorem s16c13bcA_minusB_apply_eq_zero {i j : Fin (n - 1)}
    {r : Fin (n - 1) ⊕ Fin (n - 1)} (hi : minusIdx r ≠ i) (hj : minusIdx r ≠ j) :
    (minusB n K i j) (minusEmb n r) = 0 := by
  rcases r with c | c <;> simp_all [minusIdx, minusEmb, minusB]

private theorem s16c13bcA_dot_cross [CharP K 2] (b : K) {j k : Fin (n - 1)} (hjk : j ≠ k)
    (x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (hx : x = minusA n K j ∨ x = minusB n K j k)
    (hy : y = minusA n K k ∨ y = s16c13bcA_minusD n K j k) :
    x ⬝ᵥ (minusM n K b *ᵥ y) = 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  all_goals
    simp only [minusA, minusB, s16c13bcA_minusD]
    simp only [dotProduct_add, add_dotProduct, Matrix.mulVec_add, s16c13bcA_dot_single_inl,
      s16c13bcA_dot_single_inr, s16c13bcA_dot_single_u, s16c13bcA_dot_single_t,
      Pi.single_apply]
    simp [hjk, hjk.symm]
  all_goals
    rw [← two_eq_zero_K (K := K)]
    norm_num

theorem s16c13bcA_dot_minusA_minusA [CharP K 2] (b : K) {j k : Fin (n - 1)} (hjk : j ≠ k) :
    minusA n K j ⬝ᵥ (minusM n K b *ᵥ minusA n K k) = 0 :=
  s16c13bcA_dot_cross b hjk _ _ (Or.inl rfl) (Or.inl rfl)

theorem s16c13bcA_dot_minusA_minusD [CharP K 2] (b : K) {j k : Fin (n - 1)} (hjk : j ≠ k) :
    minusA n K j ⬝ᵥ (minusM n K b *ᵥ s16c13bcA_minusD n K j k) = 0 :=
  s16c13bcA_dot_cross b hjk _ _ (Or.inl rfl) (Or.inr rfl)

theorem s16c13bcA_dot_minusB_minusA [CharP K 2] (b : K) {j k : Fin (n - 1)} (hjk : j ≠ k) :
    minusB n K j k ⬝ᵥ (minusM n K b *ᵥ minusA n K k) = 0 :=
  s16c13bcA_dot_cross b hjk _ _ (Or.inr rfl) (Or.inl rfl)

theorem s16c13bcA_dot_minusB_minusD [CharP K 2] (b : K) {j k : Fin (n - 1)} (hjk : j ≠ k) :
    minusB n K j k ⬝ᵥ (minusM n K b *ᵥ s16c13bcA_minusD n K j k) = 0 :=
  s16c13bcA_dot_cross b hjk _ _ (Or.inr rfl) (Or.inr rfl)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
