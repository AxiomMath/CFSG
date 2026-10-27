module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPlane
import Certificates.Kernel.K36K.M12.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate36151 : ∃ E : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12, Nat.card E = 27 ∧
    ∀ A : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12, A ≤ E → CFSG.Open.IsElemAbelian 3 A →
      Nat.card A = 9 → CFSG.LocalAnalysis.UniquenessCase.UCK.Spor.PlaneOK A := KernelK36K.M12.planes_M12

end Certificates
