module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import Certificates.Kernel.McLNine.Glue
public import CFSG.Sporadic.Schreier.PairMcLCertBase

public section

namespace Certificates

theorem certificate744101 :     ∃ U P Q : Subgroup ↥CFSG.Sporadic.Schreier.mclP, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧
      U ≤ P ∧ Nat.card P = 9 * Nat.card U ∧
      (∀ α : MulAut ↥CFSG.Sporadic.Schreier.mclP,
        U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) ∧
      Q ≤ P ∧ Nat.card Q = 9 ∧ ∀ q ∈ Q, q ^ 3 = 1 :=
  CertificateChecks.KernelSpor.McLNine.package744101

end Certificates
