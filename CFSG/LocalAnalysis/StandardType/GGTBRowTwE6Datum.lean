module

public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatumOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Parity
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Rank
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Weyl
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_rowR6
    (hRig : GGLabelRigidInput) :
    GGExcReflTBWeylDatumQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR6 p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  have hp3 : p ≠ 3 := ggTBRowR6_p_ne_three hL
  obtain ⟨hp, hBs, -, -, -⟩ := hHyp.1.tableB_facts
  have hNT : GGNoTransvection p Bs := hHyp.2.2.2.1
  have hLF : GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs L :=
    ggInnerDiagOnLabel_twE6Plus_of_rowR6 hRig hHyp hL
  have hW : GGWeylOfType p CoxeterMatrix.E₆ (ggAutomizer L Bs) := ggTwE6Row_weylOfType hHyp hLF
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  have hno6 : ∀ i j, CoxeterMatrix.E₆ i j ≠ 6 := by
    intro i j; fin_cases i <;> fin_cases j <;> decide
  have hpar : ∀ i j, i ≠ j → (CartanMatrix.E₆ i j ≠ 0 ↔
      ((i ≠ (0 : Fin 6) ∧ (![0, 3, 0, 2, 3, 4] : Fin 6 → Fin 6) i = j) ∨
        (j ≠ (0 : Fin 6) ∧ (![0, 3, 0, 2, 3, 4] : Fin 6 → Fin 6) j = i))) := by
    intro i j; fin_cases i <;> fin_cases j <;> decide
  have hdepth : ∀ i, i ≠ (0 : Fin 6) →
      (![0, 3, 1, 2, 3, 4] : Fin 6 → ℕ) ((![0, 3, 0, 2, 3, 4] : Fin 6 → Fin 6) i) <
        (![0, 3, 1, 2, 3, 4] : Fin 6 → ℕ) i := by
    intro i; fin_cases i <;> decide
  have hdet : (((CartanMatrix.E₆).det : ℤ) : ZMod p) ≠ 0 := by
    have h1 : (CartanMatrix.E₆).det = 3 := by decide +kernel
    rw [h1]
    intro h
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  have h7 : Module.finrank (ZMod p) V ≤ 7 := ggTwE6Row_finrank_le_seven hHyp hLF ιV
  have h6 : 6 ≤ Module.finrank (ZMod p) (ggReflSpan (p := p) Bs L ιV) := by
    have := ggReflSpan_card_le_finrank_of_weylOfType hp2 hNT ggIntCartan_E₆ hno6
      (![0, 3, 0, 2, 3, 4] : Fin 6 → Fin 6) 0 (![0, 3, 1, 2, 3, 4] : Fin 6 → ℕ) hpar hdepth hdet
      hW ιV
    simpa using this
  exact ggExcReflTBWeylDatum_of_weylOfType hp2 hNT (M := CoxeterMatrix.E₆)
    (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)) (by norm_num) ggIntCartan_E₆ hno6
    ![0, 3, 0, 2, 3, 4] 0 ![0, 3, 1, 2, 3, 4] hpar hdepth hW ιV (Or.inl (by omega))

end CFSG.StandardType

end
