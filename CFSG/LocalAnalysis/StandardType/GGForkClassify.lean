module

public import CFSG.LocalAnalysis.StandardType.GGForkCellsClassical
public import CFSG.LocalAnalysis.StandardType.GGForkCellsD

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem models_of_reindex {n : ℕ} {Λ : Type} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (e : Fin n ≃ Λ) {C : Matrix Λ Λ ℤ}
    (h : C = Matrix.reindex e e C₀ ∨ C = (Matrix.reindex e e C₀).transpose) :
    (∀ i j, C (e i) (e j) = C₀ i j) ∨ (∀ i j, C (e i) (e j) = C₀ j i) := by
  rcases h with h | h
  · left
    intro i j
    simp only [h, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  · right
    intro i j
    simp only [h, Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply]

theorem ggIntCartan_models {Λ : Type} {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) :
    (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧
      ((∀ i j, C (e i) (e j) = CartanMatrix.A n i j) ∨
        (2 ≤ n ∧ ((∀ i j, C (e i) (e j) = CartanMatrix.B n i j) ∨
          (∀ i j, C (e i) (e j) = CartanMatrix.C n i j))) ∨
        (4 ≤ n ∧ ∀ i j, C (e i) (e j) = CartanMatrix.D n i j))) ∨
    (∃ e : Fin 6 ≃ Λ, ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) ∨
    (∃ e : Fin 7 ≃ Λ, ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) ∨
    (∃ e : Fin 8 ≃ Λ, ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j) ∨
    (∃ e : Fin 4 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) ∨
    (∃ e : Fin 2 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.G₂ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.G₂ j i)) := by
  rcases hM with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ |
    ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · rw [hA] at hC
    rcases models_of_reindex (C₀ := CartanMatrix.A n) e
      (hC.eq_or_eq_transpose ((ggIntCartan_A n).reindex e)
        ((ggAtMostOneMultipleEdge_A n).reindex e)) with h | h
    · exact Or.inl ⟨n, e, hn, Or.inl h⟩
    · exact Or.inl ⟨n, e, hn, Or.inl fun i j =>
        (h i j).trans (congrFun (congrFun (CartanMatrix.A_transpose n) i) j)⟩
  · rw [hB] at hC
    rcases models_of_reindex (C₀ := CartanMatrix.B n) e
      (hC.eq_or_eq_transpose ((ggIntCartan_B n).reindex e)
        ((ggAtMostOneMultipleEdge_B n).reindex e)) with h | h
    · exact Or.inl ⟨n, e, hn, Or.inr (Or.inl ⟨hn2, Or.inl h⟩)⟩
    · exact Or.inl ⟨n, e, hn, Or.inr (Or.inl ⟨hn2, Or.inr fun i j =>
        (h i j).trans (congrFun (congrFun (CartanMatrix.B_transpose n) i) j)⟩)⟩
  · rw [hD] at hC
    rcases models_of_reindex (C₀ := CartanMatrix.D n) e
      (hC.eq_or_eq_transpose ((ggIntCartan_D n).reindex e)
        ((ggAtMostOneMultipleEdge_D n).reindex e)) with h | h
    · exact Or.inl ⟨n, e, hn, Or.inr (Or.inr ⟨hn4, h⟩)⟩
    · exact Or.inl ⟨n, e, hn, Or.inr (Or.inr ⟨hn4, fun i j =>
        (h i j).trans (congrFun (congrFun (CartanMatrix.D_transpose n) i) j)⟩)⟩
  · rw [hE6] at hC
    rcases models_of_reindex (C₀ := CartanMatrix.E 6) e
      (hC.eq_or_eq_transpose (ggIntCartan_E₆.reindex e)
        (ggAtMostOneMultipleEdge_E₆.reindex e)) with h | h
    · exact Or.inr (Or.inl ⟨e, h⟩)
    · exact Or.inr (Or.inl ⟨e, fun i j =>
        (h i j).trans (congrFun (congrFun (CartanMatrix.E_transpose 6) i) j)⟩)
  · rw [hE7] at hC
    rcases models_of_reindex (C₀ := CartanMatrix.E 7) e
      (hC.eq_or_eq_transpose (ggIntCartan_E₇.reindex e)
        (ggAtMostOneMultipleEdge_E₇.reindex e)) with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨e, h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨e, fun i j =>
        (h i j).trans (congrFun (congrFun (CartanMatrix.E_transpose 7) i) j)⟩))
  · rw [hE8] at hC
    rcases models_of_reindex (C₀ := CartanMatrix.E 8) e
      (hC.eq_or_eq_transpose (ggIntCartan_E₈.reindex e)
        (ggAtMostOneMultipleEdge_E₈.reindex e)) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, fun i j =>
        (h i j).trans (congrFun (congrFun (CartanMatrix.E_transpose 8) i) j)⟩)))
  · rw [hF4] at hC
    rcases models_of_reindex (C₀ := CartanMatrix.F₄) e
      (hC.eq_or_eq_transpose (ggIntCartan_F₄.reindex e)
        (ggAtMostOneMultipleEdge_F₄.reindex e)) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, Or.inl h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, Or.inr h⟩))))
  · rw [hG2] at hC
    rcases models_of_reindex (C₀ := CartanMatrix.G₂) e
      (hC.eq_or_eq_transpose (ggIntCartan_G₂.reindex e)
        (ggAtMostOneMultipleEdge_G₂.reindex e)) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, Or.inl h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, Or.inr h⟩))))

theorem ggForkRest_classify {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} {b c : Λ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hF : GGForkMatrix C b c) (hSA : ¬ GGForkShapeA C b) (hSB : ¬ GGForkShapeBCD C b) :
    ¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b) := by
  rcases ggIntCartan_models hM hC with
    ⟨n, e, hn, hA | ⟨hn2, hB | hCC⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
      ⟨e, hF4 | hF4T⟩ | ⟨e, hG | hGT⟩
  · exact (ggForkCell_A hn e hA hF).resolve_left hSA
  · exact absurd (ggForkCell_BC hn2 e (Or.inl hB) hF) hSB
  · exact absurd (ggForkCell_BC hn2 e (Or.inr hCC) hF) hSB
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
    exact (ggForkCell_D n' (by omega) e hD hF).resolve_left hSB
  · exact ggForkCell_E6 e hE6 hF
  · exact ggForkCell_E7 e hE7 hF
  · exact ggForkCell_E8 e hE8 hF
  · exact ggForkCell_F4 e hF4 hF
  · exact ggForkCell_F4T e hF4T hF
  · exact (ggForkCell_G2 e (Or.inl hG) hF).elim
  · exact (ggForkCell_G2 e (Or.inr hGT) hF).elim

end CFSG.StandardType
