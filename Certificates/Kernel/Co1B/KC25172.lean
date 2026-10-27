module

public import Certificates.Kernel.Co1B.Dag2045
public import Certificates.Kernel.Co1B.Dag24513
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.SporSch.Co1Mat

public section

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KC.Enum CFSG.KC.Co1B CFSG.KS.SporSch.M24

@[expose] noncomputable def commB (p : Nat) : Bool :=
  allN 10 fun j => eqK (mulWK p (S2.M j)) (mulWK (S2.M j) p)

@[expose] noncomputable def zOK (p : Nat) : Bool :=
  !commB p || eqK p idM || eqK p (Cent2045.D1.M 0)

end CertificateChecks.KernelCo1B.Syl2B

end
