module

public import Certificates.Data.Kernel.ASVolI.K43K7277
public import Certificates.Kernel.HMathieu.T24
import CFSG.Certificates.Kernel.Common.EachTrue
import all Init.Data.Array.Basic
import all Init.Data.List.Basic

public section

namespace CertificateChecks.KernelASVolI

open CFSG.KS.ASVolI CertificateChecks.KernelHMathieu

theorem k43_listsK : listsK T24.E = true := by
  decide +kernel

theorem k43_listsS : listsS = true := by
  decide +kernel

theorem k43_f3K : f3K T24.E = true := by
  decide +kernel

theorem k43_f3S : f3S = true := by
  decide +kernel

theorem k43_f4S : f4S = true := by
  decide +kernel

end CertificateChecks.KernelASVolI

#kc_each CertificateChecks.KernelASVolI k43f4_ (fun i => CFSG.KS.ASVolI.f4Slice i) 0 32

end
