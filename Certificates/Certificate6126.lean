module

public import Certificates.Data.Seitz77L34FCent
public meta import Certificates.Data.Seitz77L34FCent
import Certificates.Kernel.LocalComp.L34FCent.Glue

public section

namespace Certificates

theorem certificate6126 : Seitz77L34.l34FCentCheck
    (CFSG.PSL3Four.Native.enumBFS 42 CFSG.PSL3Four.Native.gTabs 241920).tabs = true :=
  CertificateChecks.KernelLC.L34FCent.fcent_true

end Certificates
