module

public import Certificates.Data.A8Nbr476
import Certificates.Kernel.A8Nbr476.Check
import CFSG.Certificates.Kernel.A8Nbr476Sound

public section

namespace Certificates

open Certificates.A8Nbr476 CertificateChecks.KernelA8N476

theorem certificate476001 : A8Nbr476.check () = true :=
  decide_eq_true (a8ClaimA_iff.mpr (CFSG.KC.A8N476.a8Claim_of ch476001_words ch476001_cover
    ch476001_mon ch476001_len ch476001_fst ch476001_exc))

end Certificates
