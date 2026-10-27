
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.Sporadic.Co1Block.PermCheckInputs
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Schreier.Co1StabFix
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import CFSG.Sporadic.Schreier.Co1OrbEnum
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.Co1XSet
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Kernel.Co1ThreeK.GlueQ
import Certificates.Kernel.Co1ThreeK.GlueCore
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
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
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

open CertificateChecks.KernelCo1ThreeK in
open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate13665 : (      (∀ w, MRep (Co1T.Native.wordL w) (Co1T.wG w : GL24)) ∧ Nat.card Co1T.Qg = 3 ^ 9 ∧
      ∀ t ∈ Co1T.Qg, orderOf t = 3 → t ∈ Subgroup.closure {x | x ∈ Co1T.aGA} ∨
        ∃ j, (j = 0 ∨ j = 1 ∨ j = 2) ∧ ∃ g : ↥GA, t = g * Co1T.root j * g⁻¹) ∧
    OPrimeCoreTrivialAt 3 ↥GA :=
  ⟨⟨fun w => wordL_repK w, card_QgK, fun _ ht hto => by
    simpa only [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.SplitData.T_eq_closure]
      using fusion_rootK ht hto⟩, oPrimeCoreTrivialAt_GAK⟩

end Certificates
