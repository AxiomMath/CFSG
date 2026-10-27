module

public import Certificates.Kernel.B45.C260394D
public import Certificates.Kernel.B45.C260394W
public import Certificates.Data.Kernel.B45Perm.RuSylSrch

public section

namespace CertificateChecks.KernelB45.C260394

open CFSG.KC.B45P.RuSyl

@[expose] noncomputable def rootS (r : Nat) : Bool := rootC CM PR WQ (WN 0) r

end CertificateChecks.KernelB45.C260394

end
