module

public import Certificates.Data.ThSevenPerfect
import Certificates.Kernel.ThCent.Perf7Glue
import Certificates.Certificate1020
import Certificates.Certificate1021
import Certificates.Certificate1022
import Certificates.Certificate16948

public section

namespace Certificates

open CertificateChecks

theorem certificate10143 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenPerfect.thPerfOK = true :=
  KernelThList.thPerfOK_K

end Certificates
