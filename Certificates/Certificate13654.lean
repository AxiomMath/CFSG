module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
import Certificates.Certificate17451
import Certificates.Kernel.BabyMonster.Fi23Fu
import Certificates.Kernel.Sporadic.Fi23Fu.Rels
public import CFSG.Sporadic.Co2Schreier.ThirdChain
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23SylowBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Fi22
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.Walter.JRFacts
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate131101Base
public import Certificates.Certificate13620Base
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

namespace CertificateChecks.Kernel13654

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 CFSG.Sporadic.Bridge
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster


theorem fuse_c : IsConj (phiB (t3 2)) (phiB (t3 0)) := by
  have e2 : phiB (t3 2) = Fi23InB.img 4 * Fi23InB.img 5 * Fi23InB.img 2 * Fi23InB.img 1 := by
    change phiB (Fi23.img 4 * Fi23.img 5 * Fi23.img 2 * Fi23.img 1) = _
    simp only [map_mul, phiB_img (by norm_num : 4 < 10), phiB_img (by norm_num : 5 < 10),
      phiB_img (by norm_num : 2 < 10), phiB_img (by norm_num : 1 < 10)]
  have e0 : phiB (t3 0) = Fi23InB.img 2 * Fi23InB.img 3 := by
    change phiB (Fi23.img 2 * Fi23.img 3) = _
    simp only [map_mul, phiB_img (by norm_num : 2 < 10), phiB_img (by norm_num : 3 < 10)]
  obtain ⟨k, hk⟩ := KernelBM.Fi23Fu.fuse_c
  rw [e2, e0]
  exact (isConj_iff.2 ⟨k, by rw [hk, mul_inv_cancel_right]⟩).symm

theorem fuse_d : IsConj (phiB (t3 3)) (phiB (t3 1)) := by
  have e3 : phiB (t3 3) = Fi23InB.img 5 * Fi23InB.img 3 * Fi23InB.img 7 * Fi23InB.img 0 *
      Fi23InB.img 6 * Fi23InB.img 1 := by
    change phiB (Fi23.img 5 * Fi23.img 3 * Fi23.img 7 * Fi23.img 0 * Fi23.img 6 * Fi23.img 1) = _
    simp only [map_mul, phiB_img (by norm_num : 5 < 10), phiB_img (by norm_num : 3 < 10),
      phiB_img (by norm_num : 7 < 10), phiB_img (by norm_num : 0 < 10),
      phiB_img (by norm_num : 6 < 10), phiB_img (by norm_num : 1 < 10)]
  obtain ⟨k, hk⟩ := KernelBM.Fi23Fu.fuse_d
  have hu : IsConj KernelBM.Fi23Fu.uB (phiB (t3 1)) := by
    rw [← Kernel17451.phiB_uJ]
    exact phiB.map_isConj KernelSpor.Fi23Fu.isConj_uJ
  rw [e3]
  exact (isConj_iff.2 ⟨k, by rw [hk, mul_inv_cancel_right]⟩).symm.trans hu

end CertificateChecks.Kernel13654

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 in
theorem certificate13654 :     IsConj (phiB (t3 2)) (phiB (t3 0)) ∧ IsConj (phiB (t3 3)) (phiB (t3 1)) :=
  ⟨Kernel13654.fuse_c, Kernel13654.fuse_d⟩

end Certificates
