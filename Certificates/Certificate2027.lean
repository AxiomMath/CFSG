module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenCheck
import Certificates.Kernel.SporSch.Ly.BS18009
import Certificates.Kernel.Census.Lift2027
import Certificates.Kernel.Census.Lift2027Neg

public section

open CFSG.ComponentClassification.UnbalancedAltSeven.Native
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch.LyBS CertificateChecks.KernelSporSch.LyBSF

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedAltSeven in
open CFSG.ComponentClassification.UnbalancedAltSeven.Native in
theorem certificate2027 : liftSquareCheck () = true := by
  unfold liftSquareCheck
  have hc : CFx 12 8 = CF 8 := by
    unfold CFx
    rw [bl (by omega)]
  have v : vld (CF 8) = true := (vCFi (by omega)).1
  simp only
  rw [b4_eq, csCF, hc, matA_eq, mulE v v, beqE (mulV v v) vA]
  exact KernelCensus.Lift2027.sq8

end Certificates
