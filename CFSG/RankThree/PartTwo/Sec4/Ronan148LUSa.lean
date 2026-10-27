module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Classical
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SuzukiReeTitsComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4Small
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Char3Export
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Minus
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddTop
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp


public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem lieComp_holds : LieComp :=
  lieComp_of_classical lieOrderBridge_holds YS08.LieQ.lieQConstrainedInner_three_holds
      (d4OuterExport_holds (trialityOddA2Comps_of_toral TriA2.a2PlusComps_holds
          TriA2.a2MinusComps_holds))
      (lieCompOn_exceptional
          (excRationalLieTypes_of_residualsD excRationalLieTypesOuterD_proved
              excRationalLieTypesF4Two_holds) (trialityOuterExport_of (trialityOddA2Comps_of_toral
                  TriA2.a2PlusComps_holds TriA2.a2MinusComps_holds))
          (excChar3Export_of_outer YS08.LieQ.lieQConstrainedInner_three_holds
              excChar3OuterExport_holds))
      (lieCompOn_suzukiReeTits
          (reeG2Char3Export_of_lieQ lieOrderBridge_holds YS08.LieQ.lieQConstrainedInner_three_holds))

theorem noA6At_of_lie {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (β : MulAut S) (hβ : β ^ 3 = 1) :
    NoA6At β :=
  noA6At_of_data fun J hJ => (lieComp_holds S hs hna idx he β hβ J hJ).1

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
