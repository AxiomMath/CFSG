module

public import Certificates.Kernel.Census.Co2R.Data
public import CFSG.Certificates.Kernel.Census.ToMainConj
import all Certificates.Kernel.Census.Co2R.Data
import all Certificates.Data.Kernel.Census.PackedRootR
import all Certificates.Data.Kernel.Census.PackedBase
import all Certificates.Data.Kernel.Census.PackedTree
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.PackedExc
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Census.ToMain
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
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

namespace CertificateChecks.KernelCensus.Co2R.Z

open CFSG.KC.Census CertificateChecks.KernelCensus.Co2R

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem kCanon : canonC 32 5 r.d = true := by quickRfl

theorem kPc : ppcOK 32 5 r.d.xs r.d.rs r.d.cjs r.d.bs = true := by quickRfl

theorem kTab : ptabOK 32 5 r.d.xs r.d.cm r.d.cs r.d.ci = true := by quickRfl

theorem kRl : Nat.beq r.d.roots.length r.d.us.size = true := by quickRfl

theorem kN : (List.range r.d.nodes.size).all (nodeF 32 r) = true := by quickRfl

theorem kLen : Nat.beq r.d.xs.length 18 = true := by quickRfl

theorem kPs : r.ps.all (fun p => Nat.blt p 32) = true := by quickRfl

theorem kPts : (List.range 32).all (fun q => Nat.blt (at' 12 r.O q) 2300 &&
    Nat.beq (at' 5 r.ix (at' 12 r.O q)) q) = true := by quickRfl

theorem kXl : Nat.beq r.xw.length r.d.xs.length = true := by quickRfl

theorem kXw : r.xw.all (fun x => x.all fun k => Nat.blt k (2 * 11)) = true := by quickRfl

theorem kRel : pcRelB 12 L base r.xw r.d.rs r.d.cjs = true := by quickRfl

theorem kRes : (r.xw.zip r.d.xs).all (fun p => resB 12 L 5 32 r.O r.ix p.1 p.2) = true := by
  quickRfl

theorem kX : rootXR 12 L base (pxs.getD 0 0) r = true := by quickRfl

theorem kCls : clsF 32 r = true := by quickRfl

theorem kLeaf : rootLeafR 12 11 L base pxs 0 r = true := by quickRfl

end CertificateChecks.KernelCensus.Co2R.Z

end
