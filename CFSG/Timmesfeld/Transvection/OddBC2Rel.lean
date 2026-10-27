module

public import CFSG.Timmesfeld.Transvection.OddBC2RelStatement
public import CFSG.Timmesfeld.Transvection.OddUnitary
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.Timmesfeld.Transvection.OddHeisTwist
import CFSG.Timmesfeld.Transvection.OddHeisRelations
import CFSG.Timmesfeld.Transvection.OddBC2Main
public import CFSG.Fischer.Assembly
public import CFSG.Fischer.Classification.Milestone
public import CFSG.Fischer.NoF25.Local
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Timmesfeld.Transvection.OddBC2Statement

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.LieType.BorelTits


theorem oddFrameHeisRelations : OddFrameHeisRelations := by
  intro H _ Δ h hML hq F _ _ _ n hFn _ hcard r hr hm P Q hF hns R hR _ _ θ hθr _ hθo hθc hθmem
    hd
  obtain ⟨e, hSM⟩ := IsMaxFrame.exists_tw_commutatorElement_ξ_map_suHeis hFn hr hm h hML hq hF
    hns hcard hR hθr hθo hθc hθmem hd
  obtain ⟨h1, h2⟩ := IsMaxFrame.commutatorElement_suHeis_of_tw hFn hr hm h hML hq hF hns hcard
    hR hθr hθo hθc hθmem hd e hSM
  cases e
  · simp only [RelBuild.tw_false] at h1 h2
    exact Or.inl ⟨h1, h2⟩
  · refine Or.inr ⟨fun u v u' v' hv hv' => ?_, fun s u v hv => ?_⟩
    · rw [h1 u v u' v' hv hv', RelBuild.tw_true, map_mul, unitaryInvolution_involutive hFn]
    · rw [h2 s u v hv, RelBuild.tw_true, RelBuild.tw_true, unitaryInvolution_involutive hFn]

theorem oddUnitaryStatement_holds : OddUnitaryStatement :=
  oddUnitaryStatement_of_heisRelations oddFrameHeisRelations

end CFSG.Timmesfeld.Transvection
