module

public import Certificates.Kernel.Co1ThreeK.DataZ

public section

namespace CertificateChecks.KernelCo1B.Bound17330

open CFSG.KC.Co1B

@[expose] noncomputable def AK : Nat := CertificateChecks.KernelCo1ThreeK.KZ.M 87
@[expose] noncomputable def BK : Nat := CertificateChecks.KernelCo1ThreeK.KZ.M 88
@[expose] noncomputable def XK : Nat := CertificateChecks.KernelCo1ThreeK.KZ.M 89
@[expose] noncomputable def ZK : Nat := CertificateChecks.KernelCo1ThreeK.KZ.M 90

@[expose] noncomputable def RS4 : List Nat :=
  (List.range 4).map fun i => CertificateChecks.KernelCo1ThreeK.KZ.M (87 + i)

@[expose] noncomputable def IS4 : List Nat :=
  (List.range 4).map fun i => CertificateChecks.KernelCo1ThreeK.KZ.MI (87 + i)

@[expose] noncomputable def PT : List Nat :=
  [AK, BK, XK, ZK, mulWK AK BK, mulWK BK AK, mulWK (mulWK AK BK) AK, mulWK (mulWK BK AK) BK,
    mulWK (mulWK AK BK) (mulWK AK BK), mulWK (mulWK AK BK) BK, mulWK (mulWK BK BK) AK,
    mulWK (mulWK AK AK) BK]

@[expose] def invW (w : List Int) : List Int := w.reverse.map Neg.neg

end CertificateChecks.KernelCo1B.Bound17330

end
