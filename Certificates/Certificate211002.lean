module

public import CFSG.Open.LocalVocabulary
import Certificates.Kernel.U62Q.Facts
public import CFSG.Fischer.T46Base

public section

namespace Certificates

open CertificateChecks

theorem certificate211002 : ∃ Q : Subgroup (Equiv.Perm (Fin 693)), Q ≤ CFSG.Fischer.T46 ∧
    Nat.card Q = 729 ∧
      ∀ E : Subgroup (Equiv.Perm (Fin 693)), E ≤ Q → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 81 := KernelU62Q.sylow_main

end Certificates
