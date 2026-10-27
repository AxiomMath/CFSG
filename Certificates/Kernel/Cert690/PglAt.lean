module

public import Certificates.Data.Kernel.Cert690.Pgl
public import Certificates.Kernel.Cert690.PglData

public section

namespace CertificateChecks.KernelC690.Pgl

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

@[expose] noncomputable def f10I (k : Nat) : Bool :=
  f10At K.toArray (invsL K).toArray (f10Vecs.getD k 0)

@[expose] noncomputable def f11I (k : Nat) : Bool := f11At K.toArray ((outersL K K0).getD k 0)

end CertificateChecks.KernelC690.Pgl

end
