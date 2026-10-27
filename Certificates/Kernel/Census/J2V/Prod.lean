module

public import Certificates.Kernel.Census.J2V.Pack
public import Certificates.Data.Kernel.J2V

public section

namespace CertificateChecks.KernelJ2V

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2V

@[expose] noncomputable def prodRows (a m : Nat) : Bool :=
  allN m fun i => allN 128 fun j =>
    Nat.beq (pcomp 315 9 (mask 9) (VP (a + i)) (VP j)) (VP (tabT vTt (a + i) j))

end CertificateChecks.KernelJ2V
