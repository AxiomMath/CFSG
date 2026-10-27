
module


public import CFSG.Sporadic.Recognition.LyonsAmalgamGlue
public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueInputs
import CFSG.Sporadic.Recognition.LyonsAmalgamCertBase
import CFSG.Sporadic.Recognition.LyonsModelCert
import Certificates.Kernel.LyGlue.Facts15

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.LyonsSims

open CFSG.Sporadic.Recognition.LyonsSims in
theorem certificate6113 :     Nat.card Ly0.Y0 ≤ 349920 → Nat.card Ly0.Tx ≤ 7776 → Nat.card Ly0.Txy ≤ 3888 →
      ∃ M : ModelGlue, ∀ i : Fin 4, M.txW i = Glue.txWords.getD i.val [] :=
  fun hcY hcT hcK => KernelLy.exists_modelGlue Ly0.modelChecks_of_certificate yOK_of_certificate
    trCheck_eq_true hcY hcT hcK

end Certificates
