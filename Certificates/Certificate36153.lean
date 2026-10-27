module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPlane
import Certificates.Kernel.K36K.J2.Glue
public import CFSG.Sporadic.Schreier.PairJ2CertBase

public section

namespace Certificates

open CertificateChecks

theorem certificate36153 : (∃ E : Subgroup ↥CFSG.Sporadic.Schreier.j2P, Nat.card E = 27 ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.Schreier.j2P, A ≤ E → CFSG.Open.IsElemAbelian 3 A →
        Nat.card A = 9 → Subgroup.closure (CFSG.LocalAnalysis.UniquenessCase.UCK.Spor.centSet A) = ⊤) ∧
    (∃ E : Subgroup ↥CFSG.Sporadic.Schreier.j2P, Nat.card E = 25 ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.Schreier.j2P, A ≤ E → CFSG.Open.IsElemAbelian 5 A →
        Nat.card A = 25 → Subgroup.closure (CFSG.LocalAnalysis.UniquenessCase.UCK.Spor.centSet A) = ⊤) :=
  ⟨KernelK36K.J2.planes_j2P_three, KernelK36K.J2.planes_j2P_five⟩

end Certificates
