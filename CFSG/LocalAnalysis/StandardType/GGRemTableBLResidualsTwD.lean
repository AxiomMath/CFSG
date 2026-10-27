module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActMain
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggBstarInnerDiagLInputOn_of_not_twDField
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInnerDiagLInputOn fun p lab => S p lab ∧ ¬ GGOrthLTwDFieldLabel p lab) :
    GGBstarInnerDiagLInputOn S := by
  have hF := ggBstarInnerDiagLInputOn_of_le_twDField
    (S := fun p lab => S p lab ∧ GGOrthLTwDFieldLabel p lab) fun _ _ h => h.2
  have h' := hF.or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · by_cases hl : GGOrthLTwDFieldLabel p lab
    · exact Or.inl ⟨hlab, hl⟩
    · exact Or.inr ⟨hlab, hl⟩
  · rcases hlab with h1 | h1
    · exact h1.1
    · exact h1.1

end CFSG.StandardType

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggRemainderTableBL_of_residualsUATLABCDEFG
    (hCx : GGTableBCxInputOn fun p lab =>
      ((((GGRemainderTableBLResCx p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) ∧
          ¬ GGLinTwoLabel p lab) ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) ∧
        ¬ GGUnitDvdLabelNo63 p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab)
    (hMod : GGTableBModuleInputOn fun p lab =>
      ((((GGRemainderTableBLResCx p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) ∧
          ¬ GGLinTwoLabel p lab) ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) ∧
        ¬ GGUnitDvdLabelNo63 p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab)
    (hAct : GGTableBActionInputOn fun p lab =>
      (((((GGRemainderTableBLResAct p lab ∧ ¬ GGLinDvdLabel p lab) ∧
          ¬ GGUnitDvdCoprimeNLabel p lab) ∧ ¬ GGLinTwoLabel p lab) ∧
          ¬ GGUnitDvd63CoprimeNLabel p lab) ∧ ¬ GGUnitDvdLabelNo63 p lab) ∧
        ¬ GGOrthLTwDFieldLabel p lab)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hLID : GGBstarInnerDiagLInputOn fun p lab =>
      (((GGRemainderTableBLResLID p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) ∧
        ¬ GGTwE6FieldLabel p lab) ∧ ¬ GGE6ThreeFieldLabel p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab)
    (hTv : GGLTransvectionCenterInputOn fun p lab =>
      (GGRemainderTableBLResTv p lab ∧ ¬ GGUnitaryTvResLabel p lab) ∧ ¬ GGLinTwoLabel p lab)
    (hLineN : GGLNoInvariantLineInputOn fun p lab =>
      GGRemainderTableBLResLine p lab ∧ ¬ GGUnitDvdLabel p lab ∧ ¬ GGLinTwoLabel p lab) :
    GGRemainderTableBL :=
  have hD : GGBstarInnerDiagLInputOn GGOrthLTwDFieldLabel :=
    ggBstarInnerDiagLInputOn_twDField_holds
  have hF : GGBstarInnerDiagLInputOn GGUnitDvdFieldLabel :=
    ggBstarInnerDiagLInputOn_of_le_unitDvdField fun _ _ h => h
  ggRemainderTableBL_of_residualsUATLQ
    (ggTableBCxInputOn_of_not_linTwo
      (ggTableBCxInputOn_of_not_unitDvd63CoprimeN
        (ggTableBCxInputOn_of_not_unitDvdNo63 hF (ggTableBCxInputOn_of_not_twDField hD hCx))))
    (ggTableBModuleInputOn_of_not_linTwo
      (ggTableBModuleInputOn_of_not_unitDvd63CoprimeN
        (ggTableBModuleInputOn_of_not_unitDvdNo63 hF
          (ggTableBModuleInputOn_of_not_twDField hD hMod))))
    (ggTableBActionInputOn_of_not_unitDvdCoprimeN
      (ggTableBActionInputOn_of_not_linTwo
        (ggTableBActionInputOn_of_not_unitDvd63CoprimeN
          (ggTableBActionInputOn_of_not_unitDvdNo63 hF
            (ggTableBActionInputOn_of_not_twDField hD hAct)))))
    (ggBstarInnerDiagLInputOn_of_not_unitDvdNo63
      (ggBstarInnerDiagLInputOn_of_not_twE6Field hX
        (ggBstarInnerDiagLInputOn_of_not_e6ThreeField hY
          (ggBstarInnerDiagLInputOn_of_not_twDField hLID))))
    hTv Line63.H5.line63Q2_holds hLineN

end CFSG.Yardstones.M3f9567aba59d
