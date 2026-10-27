module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import Certificates.Kernel.McLThree.Glue
public import CFSG.Sporadic.Schreier.PairMcLCertBase

public section

namespace Certificates

theorem certificate744105 :     ∃ (U P : Subgroup ↥CFSG.Sporadic.Schreier.mclP) (a g : ↥CFSG.Sporadic.Schreier.mclP),
      CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ Nat.card P = 3 * Nat.card U ∧
      (∀ α : MulAut ↥CFSG.Sporadic.Schreier.mclP,
        U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) ∧
      a ∈ P ∧ a ≠ 1 ∧ a ^ 3 = 1 ∧ g * a * g⁻¹ = a⁻¹ :=
  CertificateChecks.KernelSpor.McLThree.package744105

end Certificates
