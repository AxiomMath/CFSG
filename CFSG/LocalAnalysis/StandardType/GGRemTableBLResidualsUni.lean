module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitCopResiduals
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSix
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Certs


theorem ggBstarInnerDiagLInputOn_of_not_unitDvd63Field {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInnerDiagLInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63FieldLabel p lab) :
    GGBstarInnerDiagLInputOn S := by
  have hF := ggBstarInnerDiagLInputOn_of_le_unitDvd63Field
    (S := fun p lab => S p lab ∧ GGUnitDvd63FieldLabel p lab) fun _ _ h => h.2
  have h' := hF.or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · by_cases hl : GGUnitDvd63FieldLabel p lab
    · exact Or.inl ⟨hlab, hl⟩
    · exact Or.inr ⟨hlab, hl⟩
  · rcases hlab with h1 | h1
    · exact h1.1
    · exact h1.1

theorem ggLTransvectionCenterInputOn_of_not_unitDvd63 {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab =>
      S p lab ∧ ¬ (GGUnitDvd63Label p lab ∧ lab.n ≠ 1)) :
    GGLTransvectionCenterInputOn S := by
  have h' := (ggLTransvectionCenterInputOn_unitDvd63_of
    Line63.H5.ggUnitDvd63BstarRankInput_holds).or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGUnitDvd63Label p lab ∧ lab.n ≠ 1
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

end Certs

end CFSG.StandardType

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggRemainderTableBL_of_residualsUni
    (hCx : GGTableBCxInputOn fun p lab =>
      ((((((GGRemainderTableBLResCx p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) ∧
          ¬ GGLinTwoLabel p lab) ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) ∧
        ¬ GGUnitDvdLabelNo63 p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab) ∧
        ¬ GGUnitCopFieldLabel p lab) ∧ ¬ GGUnitDvd63Label p lab)
    (hMod : GGTableBModuleInputOn fun p lab =>
      ((((((GGRemainderTableBLResCx p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) ∧
          ¬ GGLinTwoLabel p lab) ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) ∧
        ¬ GGUnitDvdLabelNo63 p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab) ∧
        ¬ GGUnitCopFieldLabel p lab) ∧ ¬ GGUnitDvd63Label p lab)
    (hAct : GGTableBActionInputOn fun p lab =>
      (((((((GGRemainderTableBLResAct p lab ∧ ¬ GGLinDvdLabel p lab) ∧
          ¬ GGUnitDvdCoprimeNLabel p lab) ∧ ¬ GGLinTwoLabel p lab) ∧
          ¬ GGUnitDvd63CoprimeNLabel p lab) ∧ ¬ GGUnitDvdLabelNo63 p lab) ∧
        ¬ GGOrthLTwDFieldLabel p lab) ∧ ¬ GGUnitCopFieldLabel p lab) ∧ ¬ GGUnitDvd63Label p lab)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hLID : GGBstarInnerDiagLInputOn fun p lab =>
      (((((GGRemainderTableBLResLID p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) ∧
        ¬ GGTwE6FieldLabel p lab) ∧ ¬ GGE6ThreeFieldLabel p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab) ∧
        ¬ GGUnitCopFieldLabel p lab) ∧ ¬ GGUnitDvd63FieldLabel p lab)
    (hTv : GGLTransvectionCenterInputOn fun p lab =>
      ((GGRemainderTableBLResTv p lab ∧ ¬ GGUnitaryTvResLabel p lab) ∧ ¬ GGLinTwoLabel p lab) ∧
        ¬ (GGUnitDvd63Label p lab ∧ lab.n ≠ 1))
    (hLineN : GGLNoInvariantLineInputOn fun p lab =>
      GGRemainderTableBLResLine p lab ∧ ¬ GGUnitDvdLabel p lab ∧ ¬ GGLinTwoLabel p lab) :
    GGRemainderTableBL :=
  ggRemainderTableBL_of_residualsUATLABCDEFGUC (ggTableBCxInputOn_of_not_unitDvd63_holds hCx)
    (ggTableBModuleInputOn_of_not_unitDvd63_holds hMod)
    (ggTableBActionInputOn_of_not_unitDvd63_holds hAct) hX hY
    (ggBstarInnerDiagLInputOn_of_not_unitDvd63Field hLID)
    (ggLTransvectionCenterInputOn_of_not_unitDvd63 hTv) hLineN

end CFSG.Yardstones.M3f9567aba59d
