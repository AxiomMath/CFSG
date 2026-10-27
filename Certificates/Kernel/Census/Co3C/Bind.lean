module

public import Certificates.Kernel.Census.Co3C.Data
public import Certificates.Kernel.Sporadic.Co3.C
public import CFSG.Certificates.Kernel.Census.ToMainConj
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.Certificates.Kernel.Census.PidProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo3Tests
import all Certificates.Kernel.Census.Co3C.Data
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.SiftEq
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
public import CFSG.Sporadic.Schreier.Co3OrderCheck

public section

namespace CertificateChecks.KernelCensus.Co3C

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Co3 CFSG.Sporadic.Schreier.Co3

set_option maxRecDepth 1000000

@[expose] noncomputable def inP (P : Nat) : Bool := CertificateChecks.KernelSpor.Co3C.sift P

theorem inP_eq {P : Nat} (hP : canon1 276 9 P = true) (hv : pvalid 276 9 P = true) :
    inP P = co3InP (unpackP 276 9 P) := by
  have hG : Nat.shiftRight P (276 * 9) = 0 := by
    simpa [canon1] using hP
  unfold inP CertificateChecks.KernelSpor.Co3C.sift co3InP
  exact (siftK_eq CertificateChecks.KernelSpor.Co3C.binds CertificateChecks.KernelSpor.Co3C.perm
    CertificateChecks.KernelSpor.Co3C.hl rfl hG (range_of_pvalid hv)).symm

@[expose] noncomputable def uP : Nat := pid 276 9

theorem u_eq : CFSG.Monster.B.Co2.Native.idA 276 = unpackP 276 9 uP :=
  (unpackP_pid_proved (n := 276) (w := 9) (by norm_num) (by norm_num)).1.symm

theorem kU : (canon1 276 9 uP && pvalid 276 9 uP) = true := by quickRfl

theorem kCanon : canonC 276 9 d = true := by quickRfl

theorem kX : Xs.toList.all (fun P => canon1 276 9 P && pvalid 276 9 P && inP P) = true := by
  quickRfl

theorem kW : d.xs.all (fun P => canon1 276 9 P && pvalid 276 9 P &&
    (inP P || inP (pc 276 9 uP P))) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Co3C

end
