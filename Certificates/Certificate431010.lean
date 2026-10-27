module

public import Certificates.Data.Fi22Twist
import Certificates.Kernel.Fi22Rank.Q2Facts

public section

namespace Certificates

open CFSG.RankThree.Native CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative in
theorem certificate431010 : ∀ A : Subgroup (Equiv.Perm (Fin 3510)), A ≤ Subgroup.closure (permsA 3510 (qGens 2)) →
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A < 243 :=
  CertificateChecks.KernelFi22Rank.Q2.q2_abelian

end Certificates
