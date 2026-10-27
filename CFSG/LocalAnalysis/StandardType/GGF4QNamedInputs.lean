module

import CFSG.LocalAnalysis.StandardType.GGF4QGeFourReduction
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk1
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2S2
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourJoin
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourA2PSU
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourL1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoEndsL
public import CFSG.LocalAnalysis.StandardType.GGKGPosSpStd
public import CFSG.LocalAnalysis.StandardType.GGKGPosLocalHypTw
import CFSG.LocalAnalysis.StandardType.GGTbKlTableP
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGCent
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOpp
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsAbsorb
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrbS2
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisOn
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRest
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppSp
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppPlus
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppPlusSup
import CFSG.LocalAnalysis.StandardType.GGF4N2OriginalJoin
import CFSG.LocalAnalysis.StandardType.GGF4N2OmegaKAltPlaneE6
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourS1Third
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourS2Third
import CFSG.LocalAnalysis.StandardType.GGKGPosSUTableB
import CFSG.LocalAnalysis.StandardType.GGKGPosOmegaMinusTableB
import CFSG.LocalAnalysis.StandardType.GGNewPlaneLocalAction
import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem ggSecFiveWeylF4ResInput_of_n2Route
    (hMp : GGInnerDiagMpInput) (hTP : GGNbrTablePNbrInputOn GGRegimeAm2)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M) (hLevi : GGSecFiveLeviData)
    (hA : GGSecFiveDataResAt fun M => GGIsWeylMatrixA M)
    (hB : GGSecFiveDataResAt fun M => GGIsWeylMatrixB M)
    (hD : GGSecFiveDataResAt fun M => GGIsWeylMatrixD M)
    (hE : GGSecFiveDataResAt fun M => GGIsWeylMatrixE M)
    (hG : GGSecFiveDataResAt fun M => GGIsWeylMatrixG2 M)
    (hFF : FF81bThmAAtFiveSixLab) (hG0 : FF81bG0Input)
    (hN2 : GGNewPlaneLocalActionInput → GGF4QGeFourE6FourRouteInput)
    (hLB : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hB3 : GGK0ExcB3) (hgr : GGNbrGraphInput) (hlt : GGNbrLangAxisOn GGNbrLangRestLabel)
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier) :
    GGSecFiveWeylF4ResInput := by
  have hSU : GGKGPosTwInput .PSU 6 := fun _ _ _ _ _ _ _ _ hloc =>
    KGPosSU.ggTableBPosImage_PSU_of_localHypTw hloc
  have hOmP : GGKGPosTwInput .POmegaMinus 4 := KGPosOm.ggKGPosTwInput_POmegaMinus_holds
  have hKGb : GGF4QGeFourKGPosInput .S2 := ggF4QGeFourKGPosInput_S2_of_inputs hSU hOmP
  have hRk2b : GGF4QGeFourRk2Input .S2 := ggF4QGeFourRk2Input_S2_of_kgPos hKGb
  have hNPLA : GGNewPlaneLocalActionInput :=
    ggNewPlaneLocalActionInput_of
      (ggBstarNbrNormalInput_of_lBalance hLB hJp ggLNoncyclicInput_holds) hgr
      (ggNbrFieldTransvectionInput_of_typeASplit_rest_axis
        (ggNbrLangAxisOn_notTypeASplit_of_rest hlt))
  have hPl : GGF4QGeFourOppPlusInput := ggF4QGeFourOppPlusInput_of_inputs hLB hB3 hNPLA
  have hSp : GGF4QGeFourOppSpInput := ggF4QGeFourOppSpInput_of_inputs hLB hB3 hNPLA
  have hThird : GGF4QGeFourS1ThirdInput := ggF4QGeFourS1ThirdInput_of_inputs hLB hB3 hNPLA
  have hOm : GGF4QGeFourOppOmegaInput := ggF4QGeFourOppOmegaInput_of_inputs hLB hB3 hNPLA hSU hOmP
  have hThb : GGF4QGeFourS2ThirdInput := ggF4QGeFourS2ThirdInput_of_inputs hLB hB3 hNPLA hSU hOmP
  have hMissed : GGF4QGeFourRk2MissedInput .S2 :=
    ggF4QGeFourRk2MissedInput_S2_of_third hKGb ggF4QGeFourPSUPairInput_holds hThb
  have hKCb : GGF4QGeFourKGCentInput .S2 :=
    ggF4QGeFourKGCentInput_S2 ggLNoncyclicInput_holds hTBF hFC hKGb hMissed
  have hL1b : GGF4QGeFourL1Input .S2 :=
    ggF4QGeFourL1Input_S2_of_odd hKGb ggLNoncyclicInput_holds hTBF hFC hSch
      (ggF4QGeFourL1OddInput_of_kgCent ggLNoncyclicInput_holds hLB hJp
        (ggF4QGeFourJoinInput_of_suppliers hX hTCJ hRig hTPn hA8 hraw hiso hTBF hFC hRM .S2) hKCb)
  exact ggSecFiveWeylF4ResInput_of_routeInputs hFF hG0 (ggF4QTwoEndsLInput_of_tbFix hTBF hWI)
    (ggF4QTwoEndsKInput_of_kl (ggF4QTwoEndsKlInput_of_tableP hTP)) hTBF hWI
    (ggF4QGeFourEndsInput_of_opp hX hTCJ hRig hTBF hWI hTPn hA8 hraw hiso hLB hFC hSp hOm hPl)
    (ggF4QGeFourF4Input_of_sys (ggF4QGeFourSysF4Input_of_kgPos
      (ggF4QGeFourL1Input_S1_of_odd (ggF4QGeFourKGPosInput_S1 hMp) ggLNoncyclicInput_holds hTBF hFC
        (ggF4QGeFourL1OddInput_of_kgCent ggLNoncyclicInput_holds hLB hJp
          (ggF4QGeFourJoinInput_of_suppliers hX hTCJ hRig hTPn hA8 hraw hiso hTBF hFC hRM .S1)
          (ggF4QGeFourKGCentInput_S1 hMp ggLNoncyclicInput_holds hTBF hFC)))
      (ggF4QGeFourKGPosInput_S1 hMp)
      (ggF4QGeFourOrbInput_S1_of_kgPos (ggF4QGeFourKGPosInput_S1 hMp))
      (ggF4QGeFourRk2Input_S1_of_kgPos (ggF4QGeFourKGPosInput_S1 hMp))
      (ggF4QGeFourRk2CrossInput_S1_of_missed
        (ggF4QGeFourL1Input_S1_of_odd (ggF4QGeFourKGPosInput_S1 hMp) ggLNoncyclicInput_holds
          hTBF hFC
          (ggF4QGeFourL1OddInput_of_kgCent ggLNoncyclicInput_holds hLB hJp
            (ggF4QGeFourJoinInput_of_suppliers hX hTCJ hRig hTPn hA8 hraw hiso hTBF hFC hRM .S1)
            (ggF4QGeFourKGCentInput_S1 hMp ggLNoncyclicInput_holds hTBF hFC)))
        (ggF4QGeFourRk2Input_S1_of_kgPos (ggF4QGeFourKGPosInput_S1 hMp))
        (ggF4QGeFourRk2MissedInput_S1_of_third (ggF4QGeFourKGPosInput_S1 hMp) hThird))
      (ggF4QGeFourJoinInput_of_suppliers hX hTCJ hRig hTPn hA8 hraw hiso hTBF hFC hRM .S1)))
    (ggF4QGeFourTwE6Input_of_sys (ggF4QGeFourSysTwE6Input_of_kgPos hL1b hKGb
      (ggF4QGeFourOrbInput_S2_of_kgPos hKGb) hRk2b
      (ggF4QGeFourRk2CrossInput_S2_of_missed hKGb hL1b hRk2b hMissed)
      (ggF4QGeFourJoinInput_of_suppliers hX hTCJ hRig hTPn hA8 hraw hiso hTBF hFC hRM .S2)))
    (hN2 hNPLA) hLevi hA hB hD hE hG hRM

theorem ggSecFiveWeylF4ResInput_of_named_routeCfg
    (hMp : GGInnerDiagMpInput) (hTP : GGNbrTablePNbrInputOn GGRegimeAm2)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M) (hLevi : GGSecFiveLeviData)
    (hA : GGSecFiveDataResAt fun M => GGIsWeylMatrixA M)
    (hB : GGSecFiveDataResAt fun M => GGIsWeylMatrixB M)
    (hD : GGSecFiveDataResAt fun M => GGIsWeylMatrixD M)
    (hE : GGSecFiveDataResAt fun M => GGIsWeylMatrixE M)
    (hG : GGSecFiveDataResAt fun M => GGIsWeylMatrixG2 M)
    (hFF : FF81bThmAAtFiveSixLab) (hG0 : FF81bG0Input)
    (hLB : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hB3 : GGK0ExcB3) (hgr : GGNbrGraphInput) (hlt : GGNbrLangAxisOn GGNbrLangRestLabel)
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier) :
    GGSecFiveWeylF4ResInput := by
  refine ggSecFiveWeylF4ResInput_of_n2Route hMp hTP hTBF hWI hX hTCJ hRig hTPn hA8 hraw hiso hFC hRM
    hLevi hA hB hD hE hG hFF hG0 ?_ hLB hJp hB3 hgr hlt hSch
  intro hNPLA G _ _ B Bs x L D J _ _ hq y K hNb hRC hWF4 hL hK
  exact ggF4N2_centralImage_of_routeCfg hX hTCJ hRig hTPn hA8 hraw hiso hTBF hFC hRM hLB
    hNPLA hRC hq hNb hWF4 hL hK

end CFSG.StandardType

end
