module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_sum_two_data_of_comm_top {G : Type} [Group G] [Finite G]
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = ⊤)
    {N : Subgroup (MulAut (Vtil V₀ V hV)) → Subgroup (Vtil V₀ V hV) →
      Subgroup (Vtil V₀ V hV) → Prop}
    (hS : SumOfNat N (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    ∃ I₁ I₂ : Subgroup (Vtil V₀ V hV), fixV (lBar V₀ V hV L) ≤ I₁ ∧ fixV (lBar V₀ V hV L) ≤ I₂ ∧
      I₁ ⊓ (fixV (lBar V₀ V hV L) ⊔ I₂) ≤ fixV (lBar V₀ V hV L) ∧
      I₂ ⊓ (fixV (lBar V₀ V hV L) ⊔ I₁) ≤ fixV (lBar V₀ V hV L) ∧
      fixV (lBar V₀ V hV L) ⊔ (I₁ ⊔ I₂) = ⊤ ∧
      N (lBar V₀ V hV L) I₁ (fixV (lBar V₀ V hV L)) ∧
      N (lBar V₀ V hV L) I₂ (fixV (lBar V₀ V hV L)) := by
  rw [hcomm, top_inf_eq] at hS
  obtain ⟨I, hZ, hInd, hsup, hN⟩ := hS
  have hiSup : (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 :=
    le_antisymm (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩))
      (sup_le (le_iSup I 0) (le_iSup I 1))
  refine ⟨I 0, I 1, hZ 0, hZ 1, ?_, ?_, ?_, hN 0, hN 1⟩
  · have hle : I 1 ≤ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
      le_iSup₂ (f := fun j (_ : j ≠ 0) => I j) 1 (by decide)
    exact le_trans (inf_le_inf_left _ (sup_le_sup_left hle _)) (hInd 0)
  · have hle : I 0 ≤ ⨆ (j : Fin 2) (_ : j ≠ 1), I j :=
      le_iSup₂ (f := fun j (_ : j ≠ 1) => I j) 0 (by decide)
    exact le_trans (inf_le_inf_left _ (sup_le_sup_left hle _)) (hInd 1)
  · rw [← hiSup]
    exact hsup

theorem s16k_sum_two_data (h : S16gRowCtx D V₀ V L hV)
    {N : Subgroup (MulAut (Vtil V₀ V hV)) → Subgroup (Vtil V₀ V hV) →
      Subgroup (Vtil V₀ V hV) → Prop}
    (hS : SumOfNat N (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    ∃ I₁ I₂ : Subgroup (Vtil V₀ V hV), fixV (lBar V₀ V hV L) ≤ I₁ ∧ fixV (lBar V₀ V hV L) ≤ I₂ ∧
      I₁ ⊓ (fixV (lBar V₀ V hV L) ⊔ I₂) ≤ fixV (lBar V₀ V hV L) ∧
      I₂ ⊓ (fixV (lBar V₀ V hV L) ⊔ I₁) ≤ fixV (lBar V₀ V hV L) ∧
      fixV (lBar V₀ V hV L) ⊔ (I₁ ⊔ I₂) = ⊤ ∧
      N (lBar V₀ V hV L) I₁ (fixV (lBar V₀ V hV L)) ∧
      N (lBar V₀ V hV L) I₂ (fixV (lBar V₀ V hV L)) :=
  s16k_sum_two_data_of_comm_top h.comm_top hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
