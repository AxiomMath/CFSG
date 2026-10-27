module

public import Certificates.Kernel.Census.J2.Sift
public import Certificates.Data.Kernel.Census.PackedExc
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.J2K
  "Certificates/Kernel/Census/J2/data/j2Exc.json.gz" 986709 13367254789086001873
  (j2ExcSG : Array Nat) (j2ExcRoots : Array Nat) (j2ExcNodes : Array NodeP) (j2ExcCS : ArrCertP)
  (j2ExcWCS : Array (Array ArrCertP)) (j2ExcExcs : List ExcRefP) (j2ExcE0P : Array Nat)

public section

namespace CertificateChecks.KernelCensus.J2K

open CFSG.KC.Census

@[expose] noncomputable def cNLExc : Array ArrCertP :=
  Array.mk (j2ExcNodes.toList.map fun nd => pmaskCert 315 9 nd.basis)

@[expose] noncomputable def nodeExcF (i : Nat) : Bool :=
  pnodeExcOK 315 9 [0, 4, 3] inP inP inRP false false false j2ExcCS j2ExcNodes cNLExc j2ExcWCS
    j2ExcE0P j2ExcExcs i

end CertificateChecks.KernelCensus.J2K

end
