module

public import CFSG.Quasithin.Recognition.M12AscHModelInputs
import Certificates.Kernel.Misc.Coset.C8084

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.CosetTable in
theorem certificate8084 : Finite (PG 4 ascHRels) ∧ Nat.card (PG 4 ascHRels) ≤ 192 := KernelMiscCoset.C8084.card_le

end Certificates
