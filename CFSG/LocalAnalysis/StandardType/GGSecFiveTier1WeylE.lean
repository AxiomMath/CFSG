module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
public import CFSG.Timmesfeld.RankTwo.LevisExceptional

public section

namespace CFSG.StandardType

open CFSG.Timmesfeld

@[expose] def GGIsWeylMatrixE {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  (∃ e : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e) ∨
    (∃ e : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex e) ∨
    (∃ e : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex e)

theorem coxeterMatrixE6_eq_two (i j : Fin 6) (hij : i ≠ j) (h1 : ¬ edgeE 6 i j)
    (h2 : ¬ edgeE 6 j i) : (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)).M i j = 2 := by
  fin_cases i <;> fin_cases j <;> simp_all [edgeE, CoxeterMatrix.E₆] <;> rfl

theorem coxeterMatrixE6_eq_three (i j : Fin 6) (h : edgeE 6 i j) :
    (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)).M i j = 3 := by
  fin_cases i <;> fin_cases j <;> simp_all [edgeE, CoxeterMatrix.E₆] <;> rfl

theorem coxeterMatrixE7_eq_two (i j : Fin 7) (hij : i ≠ j) (h1 : ¬ edgeE 7 i j)
    (h2 : ¬ edgeE 7 j i) : (CoxeterMatrix.E₇ : CoxeterMatrix (Fin 7)).M i j = 2 := by
  fin_cases i <;> fin_cases j <;> simp_all [edgeE, CoxeterMatrix.E₇] <;> rfl

theorem coxeterMatrixE7_eq_three (i j : Fin 7) (h : edgeE 7 i j) :
    (CoxeterMatrix.E₇ : CoxeterMatrix (Fin 7)).M i j = 3 := by
  fin_cases i <;> fin_cases j <;> simp_all [edgeE, CoxeterMatrix.E₇] <;> rfl

theorem coxeterMatrixE8_eq_two (i j : Fin 8) (hij : i ≠ j) (h1 : ¬ edgeE 8 i j)
    (h2 : ¬ edgeE 8 j i) : (CoxeterMatrix.E₈ : CoxeterMatrix (Fin 8)).M i j = 2 := by
  fin_cases i <;> fin_cases j <;> simp_all [edgeE, CoxeterMatrix.E₈] <;> rfl

theorem coxeterMatrixE8_eq_three (i j : Fin 8) (h : edgeE 8 i j) :
    (CoxeterMatrix.E₈ : CoxeterMatrix (Fin 8)).M i j = 3 := by
  fin_cases i <;> fin_cases j <;> simp_all [edgeE, CoxeterMatrix.E₈] <;> rfl

theorem GGIsWeylMatrixE.isWeylMatrix {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrixE M) :
    GGIsWeylMatrix M := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
  · exact Or.inr (Or.inl ⟨e, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩)))

theorem GGIsWeylMatrixE.le_three {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrixE M)
    (i j : ι) (hij : i ≠ j) : M.M i j ≤ 3 := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
  · rw [CoxeterMatrix.reindex_apply]
    have hij' : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    generalize e.symm i = a at hij'
    generalize e.symm j = b at hij'
    fin_cases a <;> fin_cases b <;> simp_all [CoxeterMatrix.E₆]
  · rw [CoxeterMatrix.reindex_apply]
    have hij' : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    generalize e.symm i = a at hij'
    generalize e.symm j = b at hij'
    fin_cases a <;> fin_cases b <;> simp_all [CoxeterMatrix.E₇]
  · rw [CoxeterMatrix.reindex_apply]
    have hij' : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    generalize e.symm i = a at hij'
    generalize e.symm j = b at hij'
    fin_cases a <;> fin_cases b <;> simp_all [CoxeterMatrix.E₈]

end CFSG.StandardType

end
