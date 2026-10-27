module

public import Certificates.Data.T84Quad
import Certificates.Kernel.Misc.T84.Quad
import Certificates.Kernel.Misc.T84.Checks
import CFSG.Certificates.Kernel.Misc.T84QuadSound

namespace Certificates

open CFSG.KC.Misc.T84 CertificateChecks.KernelT84Q

theorem s0L_mem_442350 : ∀ c ∈ S0L, c ∈ Certificates.Asc82NormA6.codesS0 := by
  intro c hc
  unfold Certificates.Asc82NormA6.codesS0
  rw [Finset.mem_sort, CertificateChecks.KernelMisc.T84.ch442349_s0]
  exact List.mem_toFinset.2 hc

end Certificates

public section

namespace Certificates

open CFSG.KC.Misc.T84 CertificateChecks.KernelT84Q

theorem certificate442350 : T84Quad.check () = true :=
  CFSG.KC.Misc.T84Q.check_of s0L_mem_442350 ch442350_b ch442350_t ch442350_f

end Certificates
