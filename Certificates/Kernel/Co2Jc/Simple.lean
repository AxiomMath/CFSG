module

public import CFSG.Sporadic.Co2Jc.Native.Simple
public import Certificates.Kernel.Co2Jc.Gen

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Native

theorem simple_g : gOK () = true := by
  simp only [gOK, sameActBasis, sameAct, wordAct_eq]
  decide +kernel

theorem simple_perf : perfOK () = true := by
  simp only [perfOK, sameActBasis, sameAct, wordAct_eq]
  decide +kernel

theorem simple_u : uOK () = true := by
  simp only [uOK, sameActBasis, sameAct, wordAct_eq]
  decide +kernel

theorem simple_h : hOK () = true := by
  simp only [hOK, wordAct_eq]
  decide +kernel

theorem simple_fix : fixOK () = true := by
  simp only [fixOK, wordAct_eq]
  decide +kernel

theorem simple_nc : ncOK () = true := by
  simp only [ncOK, sameActBasis, sameAct, wordAct_eq]
  decide +kernel

theorem simple_check : simpleOK () = true := by
  rw [simpleOK, simple_g, simple_perf, simple_u, simple_h, simple_fix, simple_nc]
  rfl

end CertificateChecks.KernelCo2Jc
