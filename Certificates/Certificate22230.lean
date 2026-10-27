module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23U52Action
import Certificates.Kernel.PermCent.K22230F

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GSThmB.U52 in
theorem certificate22230 : ∀ x : X₀, orderOf x = 2 →
    Nat.card (Subgroup.centralizer ({x} : Set X₀)) = 82944 ∨
      Nat.card (Subgroup.centralizer ({x} : Set X₀)) = 4608 :=
  KernelPermCent.U52.card_centralizer_of_involution

end Certificates
