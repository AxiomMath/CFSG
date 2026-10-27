module

public import Certificates.Kernel.Census.HSC.Data
public import Certificates.Kernel.Misc.Perm.HSMcL
public import CFSG.Certificates.Kernel.Census.ToMainConj
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHSTests
import all Certificates.Kernel.Census.HSC.Data
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
public import CFSG.RankThree.Native.HSMcLSmallCheck

public section

namespace CertificateChecks.KernelCensus.HSC

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.HS CFSG.RankThree.Native
open CertificateChecks.KernelMisc.HSMcL

set_option maxRecDepth 1000000

@[expose] noncomputable def inP (P : Nat) : Bool :=
  siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) C1.LR C1.TRI C1.BP 5 0 P

theorem inP_eq {P : Nat} (hP : canon1 100 7 P = true) (hv : pvalid 100 7 P = true) :
    inP P = hsInP (unpackP 100 7 P) := by
  have hG : Nat.shiftRight P (100 * 7) = 0 := by
    simpa [canon1] using hP
  unfold inP hsInP
  exact (siftK_eq c1_binds c1_perm C1.hl rfl hG (range_of_pvalid hv)).symm

@[expose] noncomputable def uP : Nat := HX.F 15

theorem u_eq : hs100Arr 15 = unpackP 100 7 uP := hs100Arr_eq 15 (by norm_num)

theorem kU : (canon1 100 7 uP && pvalid 100 7 uP) = true := by quickRfl

theorem kCanon : canonC 100 7 d = true := by quickRfl

theorem kX : Xs.toList.all (fun P => canon1 100 7 P && pvalid 100 7 P && inP P) = true := by
  quickRfl

theorem kW : d.xs.all (fun P => canon1 100 7 P && pvalid 100 7 P &&
    (inP P || inP (pc 100 7 uP P))) = true := by
  quickRfl

end CertificateChecks.KernelCensus.HSC

end
