module

public import Certificates.Data.Kernel.Co1T13K
public import Certificates.Kernel.Co1T13K.Data
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1T13K

open CFSG.KC.Co1F2 CFSG.KC.Co1BBound CFSG.KC.Co1T13K CertificateChecks.KernelCo1B
open CertificateChecks.KernelCo1B.Bound17591 (XB)

@[expose] noncomputable def C0 : List Nat := [20, 12, 18, 14, 23, 13, 21, 14, 21]

@[expose] noncomputable def ch13504a (n : Nat) : Bool :=
  Nat.beq (cntTabK (inSK XB CFSG.KD.Co1T13K.YT 139 131) CV.F (Nat.mul 13 n) 13) (getL 0 C0 n)

end CertificateChecks.KernelCo1T13K

#kc_each CertificateChecks.KernelCo1T13K.ch13504a 0 9

end
