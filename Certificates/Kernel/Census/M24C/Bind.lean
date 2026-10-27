module

public import Certificates.Kernel.Census.M24C.Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
public import CFSG.Certificates.Kernel.Census.ToMainConj
import all Certificates.Kernel.Census.M24C.Data
import all CFSG.Certificates.Kernel.Census.ToMain
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
import all CFSG.Monster.Code.Defs
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.PackedExc
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights

public section

namespace CertificateChecks.KernelCensus.M24C

open CFSG.KC.Census CFSG.KC.Enum CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.M22 CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

theorem kCanon : canonC 24 5 d = true := by quickRfl

theorem kXc : Xs.toList.all (canon1 24 5) = true := by quickRfl

theorem kGc : xg.toList.all (canon1 24 5) = true := by quickRfl

theorem kE0c : e0.toList.all (canon1 24 5) = true := by quickRfl

theorem kXs : pxsOK 24 5 xg Xs xw = true := by quickRfl

theorem kW : d.xs.all inXP = true := by quickRfl

theorem kXG : (allLt (xg.map (unpackP 24 5)).size fun k =>
    validK 24 (xg.map (unpackP 24 5))[k]! && autA (xg.map (unpackP 24 5))[k]!) = true := by
  decide +kernel

end CertificateChecks.KernelCensus.M24C

end
