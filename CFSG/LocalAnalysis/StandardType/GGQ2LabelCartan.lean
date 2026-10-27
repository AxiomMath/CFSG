module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggLC_models_of_reindex {n : ℕ} {Λ : Type} {C₀ : Matrix (Fin n) (Fin n) ℤ}
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

theorem ggQ2_label_cartan {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) :
    (labL.tag = .twA ∧ ∃ e : Fin labL.rank ≃ M.Λ,
        ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A labL.rank i j) ∨
    ((labL.tag = .B ∨ labL.tag = .C) ∧ ∃ e : Fin labL.rank ≃ M.Λ,
        ((∀ i j, M.cartan (e i) (e j) = CartanMatrix.B labL.rank i j) ∨
         (∀ i j, M.cartan (e i) (e j) = CartanMatrix.C labL.rank i j))) ∨
    ((labL.tag = .D ∨ labL.tag = .twD) ∧ ∃ e : Fin labL.rank ≃ M.Λ,
        ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D labL.rank i j) ∨
    (labL.tag = .E7 ∧ ∃ e : Fin 7 ≃ M.Λ, ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E 7 i j) ∨
    labL.tag = .F4 ∨ labL.tag = .twE6 ∨ labL.tag = .E8 := by
  unfold GGQ2TBLabel at hlab
  rcases hlab with ⟨htag, h4⟩ | ⟨htag | htag, h4⟩ | ⟨htag, heven, h4⟩ |
    ⟨htag, hodd, h4⟩ | htag | htag | htag | htag
  ·
    simp only [GGQ2LabelWeyl, htag] at hW
    obtain ⟨e, hcox⟩ := hW
    refine Or.inl ⟨htag, e, ?_⟩
    have hC := M.isCartan
    rw [hcox] at hC
    rcases ggLC_models_of_reindex (C₀ := CartanMatrix.A labL.rank) e
      (hC.eq_or_eq_transpose ((ggIntCartan_A labL.rank).reindex e)
        ((ggAtMostOneMultipleEdge_A labL.rank).reindex e)) with h | h
    · exact h
    · intro i j
      exact (h i j).trans (congrFun (congrFun (CartanMatrix.A_transpose labL.rank) i) j)
  ·
    simp only [GGQ2LabelWeyl, htag] at hW
    obtain ⟨e, hcox⟩ := hW
    refine Or.inr (Or.inl ⟨Or.inl htag, e, ?_⟩)
    have hC := M.isCartan
    rw [hcox] at hC
    rcases ggLC_models_of_reindex (C₀ := CartanMatrix.B labL.rank) e
      (hC.eq_or_eq_transpose ((ggIntCartan_B labL.rank).reindex e)
        ((ggAtMostOneMultipleEdge_B labL.rank).reindex e)) with h | h
    · exact Or.inl h
    · exact Or.inr fun i j =>
        (h i j).trans (congrFun (congrFun (CartanMatrix.B_transpose labL.rank) i) j)
  ·
    simp only [GGQ2LabelWeyl, htag] at hW
    obtain ⟨e, hcox⟩ := hW
    refine Or.inr (Or.inl ⟨Or.inr htag, e, ?_⟩)
    have hC := M.isCartan
    rw [hcox] at hC
    rcases ggLC_models_of_reindex (C₀ := CartanMatrix.B labL.rank) e
      (hC.eq_or_eq_transpose ((ggIntCartan_B labL.rank).reindex e)
        ((ggAtMostOneMultipleEdge_B labL.rank).reindex e)) with h | h
    · exact Or.inl h
    · exact Or.inr fun i j =>
        (h i j).trans (congrFun (congrFun (CartanMatrix.B_transpose labL.rank) i) j)
  ·
    simp only [GGQ2LabelWeyl, htag] at hW
    obtain ⟨e, hcox⟩ := hW
    refine Or.inr (Or.inr (Or.inl ⟨Or.inl htag, e, ?_⟩))
    have hC := M.isCartan
    rw [hcox] at hC
    rcases ggLC_models_of_reindex (C₀ := CartanMatrix.D labL.rank) e
      (hC.eq_or_eq_transpose ((ggIntCartan_D labL.rank).reindex e)
        ((ggAtMostOneMultipleEdge_D labL.rank).reindex e)) with h | h
    · exact h
    · intro i j
      exact (h i j).trans (congrFun (congrFun (CartanMatrix.D_transpose labL.rank) i) j)
  ·
    simp only [GGQ2LabelWeyl, htag] at hW
    obtain ⟨e, hcox⟩ := hW
    refine Or.inr (Or.inr (Or.inl ⟨Or.inr htag, e, ?_⟩))
    have hC := M.isCartan
    rw [hcox] at hC
    rcases ggLC_models_of_reindex (C₀ := CartanMatrix.D labL.rank) e
      (hC.eq_or_eq_transpose ((ggIntCartan_D labL.rank).reindex e)
        ((ggAtMostOneMultipleEdge_D labL.rank).reindex e)) with h | h
    · exact h
    · intro i j
      exact (h i j).trans (congrFun (congrFun (CartanMatrix.D_transpose labL.rank) i) j)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htag))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htag)))))
  ·
    simp only [GGQ2LabelWeyl, htag] at hW
    obtain ⟨e, hcox⟩ := hW
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨htag, e, ?_⟩)))
    have hC := M.isCartan
    rw [hcox] at hC
    rcases ggLC_models_of_reindex (C₀ := CartanMatrix.E 7) e
      (hC.eq_or_eq_transpose (ggIntCartan_E₇.reindex e)
        (ggAtMostOneMultipleEdge_E₇.reindex e)) with h | h
    · exact h
    · intro i j
      exact (h i j).trans (congrFun (congrFun (CartanMatrix.E_transpose 7) i) j)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr htag)))))

end CFSG.StandardType

end
