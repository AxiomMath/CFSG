module

public import Certificates.Data.Kernel.SporSch.Co1Bfs
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
public meta import Certificates.Kernel.Co1FiveK.Data
public meta import Certificates.Data.Co1FiveComp
public import Certificates.Kernel.Co1FiveK.Data

public section

namespace CertificateChecks.KernelCo1FiveComp

meta def sArr : Array (Array Nat) :=
  (Timmesfeld.Co1FiveComp.sRows CertificateChecks.KernelCo1FiveK.dagD.1
    CertificateChecks.KernelCo1FiveK.dagD.2.1).toArray

end CertificateChecks.KernelCo1FiveComp

#kss_co1gt CertificateChecks.KernelCo1FiveComp.ST CertificateChecks.KernelCo1FiveComp.sArr 100000

end
