module

public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatumOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadLabelParity
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadTbHyp
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggExcReflTBWeylDatumQFourOn_twE6Bad
    (hnc : GGTBJNoncommReflOn GGTwE6BadLabel) :
    GGExcReflTBWeylDatumQFourOn GGTwE6BadLabel := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  obtain ⟨-, hBs, -, -, -⟩ := hHyp.1.tableB_facts
  have hNT : GGNoTransvection p Bs := hHyp.2.2.2.1
  obtain ⟨a, ha, b, -, -, -, hab⟩ := hnc G p B Bs x L D J hHyp hq hN hL
  have hJ : ∃ a ∈ ggAutomizer J Bs, a ≠ 1 :=
    ⟨a, ha, fun h => hab (by rw [h, one_mul, mul_one])⟩
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  exact ggExcReflTBWeylDatum_of_weylOfType hp2 hNT (M := CoxeterMatrix.E₆)
    (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)) (by norm_num) ggIntCartan_E₆
    (by intro i j; fin_cases i <;> fin_cases j <;> decide) ![0, 3, 0, 2, 3, 4] 0
    ![0, 3, 1, 2, 3, 4] (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by intro i; fin_cases i <;> decide)
    (ggTwE6Bad_weylOfType hHyp hL) ιV (Or.inr (ggTwE6Bad_tbHyp hHyp hL hJ ιV))

theorem GGTBJNoncommReflOn.mono {S T : ℕ → LargeEvenLabel → Prop} (h : GGTBJNoncommReflOn S)
    (hTS : ∀ p lab, T p lab → S p lab) : GGTBJNoncommReflOn T :=
  fun G _ _ p B Bs x L D J hH hq hN hL => h G p B Bs x L D J hH hq hN
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hTS p _ hP.1, hP.2⟩) hL)

theorem GGExcReflTBWeylDatumQFourOn.mono {S T : ℕ → LargeEvenLabel → Prop}
    (h : GGExcReflTBWeylDatumQFourOn S) (hTS : ∀ p lab, T p lab → S p lab) :
    GGExcReflTBWeylDatumQFourOn T :=
  fun G _ _ p B Bs x L D J hH hq hN hL => h G p B Bs x L D J hH hq hN
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hTS p _ hP.1, hP.2⟩) hL)

theorem ggExcReflTBWeylDatumQFourOn_of_split (S T : ℕ → LargeEvenLabel → Prop)
    (hST : GGExcReflTBWeylDatumQFourOn fun p lab => S p lab ∧ T p lab)
    (hSN : GGExcReflTBWeylDatumQFourOn fun p lab => S p lab ∧ ¬ T p lab) :
    GGExcReflTBWeylDatumQFourOn S := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  have hL' : GGInnerDiagOnLabel (fun p lab => (S p lab ∧ T p lab) ∨ (S p lab ∧ ¬ T p lab))
      p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨hs, hP⟩ =>
      ⟨(em (T p _)).elim (fun h => Or.inl ⟨hs, h⟩) (fun h => Or.inr ⟨hs, h⟩), hP⟩) hL
  rcases hL'.elim_or with h | h
  · exact hST G p B Bs x L D J hHyp hq hN h
  · exact hSN G p B Bs x L D J hHyp hq hN h

theorem ggTBJNoncommReflOn_twE6_of_slot (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, GGLabQFour p lab → lab.tag = .twE6 → S p lab)
    (h : GGTBJNoncommReflOn S) :
    GGTBJNoncommReflOn fun p lab => lab.tag = .twE6 ∧ p = 3 := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  refine h G p B Bs x L D J hHyp hq hN ?_
  obtain ⟨labq, hlabq, hhasq, _, _, _, _, _, hPq⟩ := largeEvenMarking_exists_hasLabel hq
  obtain ⟨labT, hlabT, hhasT, _, _, _, _, _, hPT⟩ := largeEvenMarking_exists_hasLabel hL
  have heq : labq = labT :=
    eq_of_ggLabelIso_of_twE6 hPT.1.1 (hRig labq labT _ hlabq hlabT hhasq hhasT)
  have hSlab : S p labT := hS p labT (heq ▸ hPq.1) hPT.1.1
  refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlabT hhasT)
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hSlab, hBN, hBI⟩

theorem ggExcReflTBWeylDatumQFourOn_twE6
    (hRig : GGLabelRigidInput)
    (hnc : GGTBJNoncommReflOn fun p lab => lab.tag = .twE6 ∧ p = 3) :
    GGExcReflTBWeylDatumQFourOn fun p lab => lab.tag = .twE6 ∧ p = 3 := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  exact ggExcReflTBWeylDatumQFourOn_twE6Bad
    (hnc.mono fun p lab h => ⟨h.1, h.2.1⟩) G p B Bs x L D J hHyp hq hN
    (ggInnerDiagOnLabel_twE6Bad_of_three hRig hHyp hL)

theorem ggExcReflTBWeylDatumQFourOn_of_twE6Row
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, GGLabQFour p lab → lab.tag = .twE6 → S p lab) (hnc : GGTBJNoncommReflOn S)
    (hrest : GGExcReflTBWeylDatumQFourOn fun p lab => S p lab ∧ ¬ (lab.tag = .twE6 ∧ p = 3)) :
    GGExcReflTBWeylDatumQFourOn S :=
  ggExcReflTBWeylDatumQFourOn_of_split S (fun p lab => lab.tag = .twE6 ∧ p = 3)
    ((ggExcReflTBWeylDatumQFourOn_twE6 hRig
      (ggTBJNoncommReflOn_twE6_of_slot hRig hS hnc)).mono fun _ _ h => h.2) hrest

end CFSG.StandardType

end
