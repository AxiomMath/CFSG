module

public import CFSG.Sporadic.Th.Setup
public import CFSG.Open.LocalVocabulary
import Certificates.Kernel.ThLocal.E81Glue

public section

namespace Certificates

open CFSG.Sporadic.Th in
theorem certificate9521 :     ∃ (Q : Subgroup (GL (Fin 248) (ZMod 2))) (z : GL (Fin 248) (ZMod 2)), Q ≤ J ∧
      Nat.card Q = 3 ^ 10 ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ Q ∧ (∀ q ∈ Q, q * z = z * q) ∧
      ∀ s ∈ Q, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup (GL (Fin 248) (ZMod 2)), E ≤ Q ∧ CFSG.Open.IsElemAbelian 3 E ∧
          81 ≤ Nat.card E ∧ s ∈ E ∧ z ∈ E :=
  CertificateChecks.KernelThLocal.th_e81_9521

end Certificates
