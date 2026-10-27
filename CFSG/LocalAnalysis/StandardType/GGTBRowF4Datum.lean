module

public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatumOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4Parity
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4Rank
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4Weyl
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpan
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_rowR4
    (hRig : GGLabelRigidInput) :
    GGExcReflTBWeylDatumQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR4 p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  obtain ⟨-, hBs, -, -, -⟩ := hHyp.1.tableB_facts
  have hNT : GGNoTransvection p Bs := hHyp.2.2.2.1
  have hLF : GGInnerDiagOnLabel GGTableBF4Label p Bs L :=
    ggInnerDiagOnLabel_f4Split_of_rowR4 hRig hHyp hL
  have hW : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs) := ggF4Row_weylOfType hHyp hLF
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  have hno6 : ∀ i j, CoxeterMatrix.F₄ i j ≠ 6 := by
    intro i j; fin_cases i <;> fin_cases j <;> decide
  have hpar : ∀ i j, i ≠ j → (CartanMatrix.F₄ i j ≠ 0 ↔
      ((i ≠ (0 : Fin 4) ∧ (![0, 0, 1, 2] : Fin 4 → Fin 4) i = j) ∨
        (j ≠ (0 : Fin 4) ∧ (![0, 0, 1, 2] : Fin 4 → Fin 4) j = i))) := by
    intro i j; fin_cases i <;> fin_cases j <;> decide
  have hdepth : ∀ i, i ≠ (0 : Fin 4) →
      (![0, 1, 2, 3] : Fin 4 → ℕ) ((![0, 0, 1, 2] : Fin 4 → Fin 4) i) <
        (![0, 1, 2, 3] : Fin 4 → ℕ) i := by
    intro i; fin_cases i <;> decide
  have hdet : (((CartanMatrix.F₄).det : ℤ) : ZMod p) ≠ 0 := by
    have h1 : (CartanMatrix.F₄).det = 1 := by decide +kernel
    rw [h1, Int.cast_one]
    exact one_ne_zero
  have h5 : Module.finrank (ZMod p) V ≤ 5 := ggF4Row_finrank_le_five hHyp hLF ιV
  have h4 : 4 ≤ Module.finrank (ZMod p) (ggReflSpan (p := p) Bs L ιV) := by
    have := ggReflSpan_card_le_finrank_of_weylOfType hp2 hNT ggIntCartan_F₄ hno6
      (![0, 0, 1, 2] : Fin 4 → Fin 4) 0 (![0, 1, 2, 3] : Fin 4 → ℕ) hpar hdepth hdet hW ιV
    simpa using this
  exact ggExcReflTBWeylDatum_of_weylOfType hp2 hNT (M := CoxeterMatrix.F₄)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))))) (by norm_num)
    ggIntCartan_F₄ hno6 ![0, 0, 1, 2] 0 ![0, 1, 2, 3] hpar hdepth hW ιV (Or.inl (by omega))

theorem ggExcReflTBWeylDatumQFourOn_of_rowR4
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGExcReflTBWeylDatumQFourOn fun p lab => S p lab ∧ lab.tag ≠ .F4) :
    GGExcReflTBWeylDatumQFourOn S :=
  ggExcReflTBWeylDatumQFourOn_of_split S GGTBRowR4
    ((ggExcReflTBWeylDatumQFourOn_rowR4 hRig).mono fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
