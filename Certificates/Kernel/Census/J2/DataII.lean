module

public import Certificates.Kernel.Census.J2.Sift
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.J2K
  "Certificates/Kernel/Census/J2/data/j2II.json.gz" 979792 12706552235063113241
  (j2IISG : Array Nat) (j2IIRoots : Array Nat) (j2IINodes : Array NodeP) (j2IICS : ArrCertP)
  (j2IIWCS : Array (Array ArrCertP))

public section

namespace CertificateChecks.KernelCensus.J2K

open CFSG.KC.Census

@[expose] noncomputable def cNLII : Array ArrCertP :=
  Array.mk (j2IINodes.toList.map fun nd => pmaskCert 315 9 nd.basis)

@[expose] noncomputable def nodeIIF (i : Nat) : Bool :=
  pnodeOK 315 9 [0, 4, 3] inP inP false true false j2IICS j2IINodes cNLII j2IIWCS i

end CertificateChecks.KernelCensus.J2K

end
