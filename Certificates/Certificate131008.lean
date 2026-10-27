
module

public import CFSG.HardMathSupport.Foote.E27.LieThree.SpModelP
import Certificates.Kernel.E27Lie.Sp63Facts

public section

namespace Certificates

open CFSG.HardMathSupport.Foote.E27 in
theorem certificate131008 : ∃ S : Subgroup (SpJP 3 3), Nat.card S = 3 ^ (Nat.card (SpJP 3 3)).factorization 3 ∧
    ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ Subgroup.centralizer ({s} : Set (SpJP 3 3))) :=
  CertificateChecks.KernelE27Lie.Sp63.sp63_sylow

end Certificates
