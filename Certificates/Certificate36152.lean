module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPlane
import Certificates.Kernel.K36K.M22.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate36152 : ∃ E : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22, Nat.card E = 9 ∧
    ∀ A : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22, A ≤ E → CFSG.Open.IsElemAbelian 3 A →
      Nat.card A = 9 → Subgroup.closure (CFSG.LocalAnalysis.UniquenessCase.UCK.Spor.centSet A) = ⊤ := KernelK36K.M22.planes_M22

end Certificates
