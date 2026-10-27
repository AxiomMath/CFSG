module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBCertInputs2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers
public import CFSG.Sporadic.SmallOddCore.LocalSpec
import Certificates.Kernel.Census.J2V.Facts
import Certificates.Kernel.Census.J2V.Checks
import Certificates.Kernel.Census.J2V.Prod
import Certificates.Kernel.Census.J2V.Idx
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Certificate10019
import Certificates.Certificate10021
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Th.F2Spec
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import CFSG.GH74.Generic.S45.LEvSporGen
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowCheck
import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Model
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HarrisLit.EndB CFSG.ComponentClassification.J2Cover in
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore in
theorem certificate22401 : ((∀ i < 128, ∀ j < 128, vT i j < 128 ∧
        tp 315 vTbls[vT i j]! = tp 315 vTbls[i]! * tp 315 vTbls[j]!) ∧
      (∀ i < 128, vI i < 128 ∧ tp 315 vTbls[vI i]! = (tp 315 vTbls[i]!)⁻¹) ∧
      tp 315 vTbls[0]! = 1 ∧ tp 315 vTbls[1]! = permTwoA ∧
      (∀ i < 128, ∀ j < 128, tp 315 vTbls[i]! = tp 315 vTbls[j]! → i = j) ∧
      (∀ k < 128, tp 315 vTbls[k]! ∈ centralizerIn P permTwoA) ∧
      (∀ k < 128, vCu k < 128 ∧
        tp 315 u0Tbl * tp 315 vTbls[k]! * (tp 315 u0Tbl)⁻¹ = tp 315 vTbls[vCu k]!) ∧
      vUsq < 128 ∧ tp 315 u0Tbl * tp 315 u0Tbl = tp 315 vTbls[vUsq]!) ∧
    subIndexCheck = true := KernelJ2V.facts22401

end Certificates
