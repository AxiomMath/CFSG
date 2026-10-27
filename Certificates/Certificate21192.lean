module

public import CFSG.CGT.M24R.N8Inputs
import Certificates.Kernel.N8.Assembly

public section

namespace Certificates

open CertificateChecks

open CFSG.CGT.M24R CFSG.CosetTable in
theorem certificate21192 : (Finite (PG 10 relsN8Ten) ∧ Nat.card (PG 10 relsN8Ten) ≤ 322560) ∧
    glCountCheck = true ∧
    ∃ W : List (List (Fin 6)), W.length = 20160 ∧ (W.map evalM8).Nodup := N8K.proof21192

end Certificates
