module

public import CFSG.Quasithin.Recognition.M12AscCoxInputs
import Certificates.Kernel.Misc.Coset.C8083

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.CosetTable in
theorem certificate8083 : Finite (PG 5 (coxRels 5)) ∧ Nat.card (PG 5 (coxRels 5)) ≤ 720 := KernelMiscCoset.C8083.card_le

end Certificates
