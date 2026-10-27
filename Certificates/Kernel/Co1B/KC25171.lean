module

public import Certificates.Kernel.Co1B.Dag2047
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.SporSch.Co1Mat

public section

namespace CertificateChecks.KernelCo1B.C25171

open CFSG.KC.Enum CFSG.KC.Co1B CFSG.KS.SporSch.M24

@[expose] noncomputable def commC (p : Nat) : Bool :=
  allN 8 fun j => eqK (mulWK p (C2047.D2.M j)) (mulWK (C2047.D2.M j) p)

@[expose] noncomputable def zOKC (p : Nat) : Bool :=
  !commC p || eqK p idM || eqK p (C2047.D1.M 2)

end CertificateChecks.KernelCo1B.C25171

end
