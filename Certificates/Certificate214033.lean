module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs
public import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import Certificates.Certificate2043
public import Certificates.Certificate2133
public import Certificates.Certificate2135
public import Certificates.Certificate2147
public import Certificates.Certificate2148
public import Certificates.Certificate2150
public import Certificates.Certificate3024
import Certificates.Kernel.Co1Pairs.Glue
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
import CFSG.Assembly.QuasithinDefs
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.Monster.AxisCount.HSIdentBaby
import CFSG.Monster.AxisCount.HSIdentRec0
import CFSG.Monster.AxisCount.HSIdentRec1
import CFSG.Monster.AxisCount.HSIdentRec2
import CFSG.Monster.AxisCount.HSIdentRec3
import CFSG.Monster.AxisCount.HSIdentRec4
import CFSG.Monster.AxisCount.HSIdentRec5
import CFSG.Monster.AxisCount.HSIdentRec6
import CFSG.Monster.AxisCount.HSIdentRec7
import CFSG.Monster.AxisCount.HSIdentSmall
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.Sporadic.Bridge.M11CheckInputs
import CFSG.Sporadic.Co1.Module.InvPermChar
import CFSG.Sporadic.FischerOddCore.Basic
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Sporadic.Schreier.J1QT
import CFSG.Sporadic.Schreier.LyFixedSet
import CFSG.Sporadic.Schreier.RuLocal
import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
import CFSG.Sporadic.SmallOddCore.CentSpec
import CFSG.Sporadic.ThSchreier.ThSchreierCase
import CFSG.YGroups.DCE.B433Check
import Certificates.Certificate10027
import Certificates.Certificate10107
import Certificates.Certificate10108
import Certificates.Certificate10110
import Certificates.Certificate10111
import Certificates.Certificate16018
import Certificates.Certificate2323
import Certificates.Certificate6006
import Certificates.Certificate8026Base
import Certificates.Certificate9124

public section

namespace Certificates

open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate214033 :     (orderOf (Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0]) = 3 ∧ ∃ a b : ↥GA,
      a * Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] * a ∧
      b * Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] * b ∧
      orderOf a = 7 ∧ orderOf b = 7 ∧
      13 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) ∧
    (orderOf (Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0]) = 3 ∧ ∃ a b : ↥GA,
      a * Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] * a ∧
      b * Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] * b ∧
      orderOf a = 7 ∧ orderOf b = 7 ∧
      81 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) ∧
    (orderOf (Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0]) = 3 ∧ ∃ a b : ↥GA,
      a * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] * a ∧
      b * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] * b ∧
      orderOf a = 5 ∧ orderOf b = 5 ∧
      81 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) ∧
    (orderOf (Co1T.root 2) = 3 ∧ ∃ a b : ↥GA, a * Co1T.root 2 = Co1T.root 2 * a ∧
      b * Co1T.root 2 = Co1T.root 2 * b ∧ orderOf a = 7 ∧ orderOf b = 7 ∧
      81 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) :=
  CertificateChecks.KernelCo1Pairs.facts214033

end Certificates
