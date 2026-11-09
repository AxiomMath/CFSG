module

public import Certificates.Kernel.Census.Co2R.Sub
public import CFSG.Certificates.Kernel.Common.EachTrue
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

#kc_each CertificateChecks.KernelCensus.Co2R.U kq
  (fun k => CertificateChecks.KernelCensus.Co2R.invChunk 24 CertificateChecks.KernelCensus.Co2R.U.r 4096 k) 0 8

namespace CertificateChecks.KernelCensus.Co2R.U

open CFSG.KC.Census CertificateChecks.KernelCensus.Co2R

set_option maxRecDepth 1000000

theorem kCanon : canonC 24 5 r.d = true := by quickRfl

theorem kPc : ppcOK 24 5 r.d.xs r.d.rs r.d.cjs r.d.bs = true := by quickRfl

theorem kInvH : invHead 24 r = true := by quickRfl

theorem kInv : pinvOK 24 5 r.d.xs r.d.us r.d.im r.d.wt = true :=
  pinvOKQ_of_chunks (K := 8) (S := 4096) kInvH
    (by rw [Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq r.d.xs.length 15 = true)]; decide)
    fun c hc => match c, hc with
      | 0, _ => kq0 | 1, _ => kq1 | 2, _ => kq2 | 3, _ => kq3
      | 4, _ => kq4 | 5, _ => kq5 | 6, _ => kq6 | 7, _ => kq7
      | _ + 8, h => absurd h (by omega)

theorem kTab : ptabOK 24 5 r.d.xs r.d.cm r.d.cs r.d.ci = true := by quickRfl

theorem kRl : Nat.beq r.d.roots.length r.d.us.size = true := by quickRfl

theorem kR : (r.d.us.toList.zip r.d.roots).all
    (fun ur => prootOKC 24 5 (r.d.nodes.map NodeP.basis) (cN 24 r) r.d.cs r.d.ci ur.1 ur.2) =
      true := by quickRfl

theorem kN : (List.range r.d.nodes.size).all (nodeF 24 r) = true := by quickRfl

theorem kLen : Nat.beq r.d.xs.length 15 = true := by quickRfl

theorem kPs : r.ps.all (fun p => Nat.blt p 24) = true := by quickRfl

theorem kPts : (List.range 24).all (fun q => Nat.blt (at' 12 r.O q) 2300 &&
    Nat.beq (at' 5 r.ix (at' 12 r.O q)) q) = true := by quickRfl

theorem kXl : Nat.beq r.xw.length r.d.xs.length = true := by quickRfl

theorem kXw : r.xw.all (fun x => x.all fun k => Nat.blt k (2 * 11)) = true := by quickRfl

theorem kRel : pcRelB 12 L base r.xw r.d.rs r.d.cjs = true := by quickRfl

theorem kRes : (r.xw.zip r.d.xs).all (fun p => resB 12 L 5 24 r.O r.ix p.1 p.2) = true := by
  quickRfl

theorem kX : rootXR 12 L base (pxs.getD 2 0) r = true := by quickRfl

theorem kCls : clsF 24 r = true := by quickRfl

theorem kLeaf : rootLeafR 12 11 L base pxs 2 r = true := by quickRfl

end CertificateChecks.KernelCensus.Co2R.U

end
