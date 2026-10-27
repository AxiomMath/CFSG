module

public import Certificates.Data.E27.LyS0
import Certificates.Kernel.LyS0.Facts

public section

namespace Certificates

theorem certificate131100 : CFSG.Sporadic.Ly.S0.lyS0Check () = true :=
  CertificateChecks.KernelLyS0.lyS0Check_true

end Certificates
