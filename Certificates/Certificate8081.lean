module

public import CFSG.Quasithin.Recognition.CertU33PresInputs
import Certificates.Kernel.Misc.Coset.C8081

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.CosetTable in
theorem certificate8081 : Finite (PG 5 u33PresRels) ∧ Nat.card (PG 5 u33PresRels) ≤ 6048 := KernelMiscCoset.C8081.card_le

end Certificates
