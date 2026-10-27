module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

variable {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}

private theorem cartan_of_simplyLaced {n : ℕ} {M₀ : CoxeterMatrix (Fin n)}
    {C₀ : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ) (hM : M = M₀.reindex e)
    (hC : GGIntCartan M C) (hC₀ : GGIntCartan M₀ C₀)
    (hle : ∀ i j : Fin n, i ≠ j → M₀ i j ≤ 3) :
    ∀ i j : Fin n, C (e i) (e j) = C₀ i j := by
  have hC' : GGIntCartan M (Matrix.reindex e e C₀) := by
    rw [hM]
    exact hC₀.reindex e
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hC.1, hC₀.1]
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hMle : M (e i) (e j) ≤ 3 := by
      rw [hM, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact hle i j hij
    have hpair := (GGIntCartan.pair hC hC' hne).2 hMle
    rw [hpair.1]
    change C₀ (e.symm (e i)) (e.symm (e j)) = C₀ i j
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem ggQ2_cartan_A {n : ℕ} (e : Fin n ≃ Λ) (hM : M = (CoxeterMatrix.A n).reindex e)
    (hC : GGIntCartan M C) : ∀ i j : Fin n, C (e i) (e j) = CartanMatrix.A n i j := by
  refine cartan_of_simplyLaced e hM hC (ggIntCartan_A n) ?_
  intro i j hij
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  rw [if_neg hij]
  split_ifs <;> omega

theorem ggQ2_cartan_D {n : ℕ} (e : Fin n ≃ Λ) (hM : M = (ggCoxeterMatrixD n).reindex e)
    (hC : GGIntCartan M C) : ∀ i j : Fin n, C (e i) (e j) = CartanMatrix.D n i j := by
  refine cartan_of_simplyLaced e hM hC (ggIntCartan_D n) ?_
  intro i j hij
  rw [ggCoxeterMatrixD_apply, if_neg hij]
  split_ifs <;> omega

theorem ggQ2_cartan_E₆ (e : Fin 6 ≃ Λ) (hM : M = CoxeterMatrix.E₆.reindex e)
    (hC : GGIntCartan M C) : ∀ i j : Fin 6, C (e i) (e j) = CartanMatrix.E₆ i j := by
  refine cartan_of_simplyLaced e hM hC ggIntCartan_E₆ ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

theorem ggQ2_cartan_E₇ (e : Fin 7 ≃ Λ) (hM : M = CoxeterMatrix.E₇.reindex e)
    (hC : GGIntCartan M C) : ∀ i j : Fin 7, C (e i) (e j) = CartanMatrix.E₇ i j := by
  refine cartan_of_simplyLaced e hM hC ggIntCartan_E₇ ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

theorem ggQ2_cartan_E₈ (e : Fin 8 ≃ Λ) (hM : M = CoxeterMatrix.E₈.reindex e)
    (hC : GGIntCartan M C) : ∀ i j : Fin 8, C (e i) (e j) = CartanMatrix.E₈ i j := by
  refine cartan_of_simplyLaced e hM hC ggIntCartan_E₈ ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma cartanC_apply (n : ℕ) (i j : Fin n) :
    CartanMatrix.C n i j = CartanMatrix.B n j i := by
  simp only [CartanMatrix.B, CartanMatrix.C, Matrix.of_apply]
  split_ifs <;> omega

theorem ggQ2_cartan_B {n : ℕ} (e : Fin n ≃ Λ) (hM : M = (CoxeterMatrix.B n).reindex e)
    (hC : GGIntCartan M C) :
    (∀ i j : Fin n, C (e i) (e j) = CartanMatrix.B n i j) ∨
      (∀ i j : Fin n, C (e i) (e j) = CartanMatrix.C n i j) := by
  have hCB : GGIntCartan M (Matrix.reindex e e (CartanMatrix.B n)) := by
    rw [hM]
    exact (ggIntCartan_B n).reindex e
  have hone : GGAtMostOneMultipleEdge M := by
    rw [hM]
    exact (ggAtMostOneMultipleEdge_B n).reindex e
  rcases GGIntCartan.eq_or_eq_transpose hC hCB hone with h | h
  · left
    intro i j
    rw [h]
    change CartanMatrix.B n (e.symm (e i)) (e.symm (e j)) = CartanMatrix.B n i j
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · right
    intro i j
    rw [h, Matrix.transpose_apply]
    change CartanMatrix.B n (e.symm (e j)) (e.symm (e i)) = CartanMatrix.C n i j
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact (cartanC_apply n i j).symm

theorem ggQ2_cartan_F₄ (e : Fin 4 ≃ Λ) (hM : M = CoxeterMatrix.F₄.reindex e)
    (hC : GGIntCartan M C) :
    (∀ i j : Fin 4, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j : Fin 4, C (e i) (e j) = CartanMatrix.F₄ j i) := by
  have hCF : GGIntCartan M (Matrix.reindex e e CartanMatrix.F₄) := by
    rw [hM]
    exact (ggIntCartan_F₄).reindex e
  have hone₀ : GGAtMostOneMultipleEdge CoxeterMatrix.F₄ := by
    refine ggAtMostOneMultipleEdge_of_pair (1 : Fin 4) 2 ?_
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.F₄]
  have hone : GGAtMostOneMultipleEdge M := by
    rw [hM]
    exact hone₀.reindex e
  rcases GGIntCartan.eq_or_eq_transpose hC hCF hone with h | h
  · left
    intro i j
    rw [h]
    change CartanMatrix.F₄ (e.symm (e i)) (e.symm (e j)) = CartanMatrix.F₄ i j
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · right
    intro i j
    rw [h, Matrix.transpose_apply]
    change CartanMatrix.F₄ (e.symm (e j)) (e.symm (e i)) = CartanMatrix.F₄ j i
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end CFSG.StandardType

end
