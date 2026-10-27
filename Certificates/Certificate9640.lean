module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48SylowGroup
import Certificates.Kernel.CertF8.Glue9640

public section

namespace Certificates

open CFSG.AGLEmbedding.ChevOuterD48 in
theorem certificate9640 : Nat.card sylowGroup = 3 ^ 6 ∧
    ∀ E : Subgroup (GL (Fin 8) GF512), E ≤ sylowGroup → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 2 := Kernel.CertF8.C9640.facts9640

end Certificates
