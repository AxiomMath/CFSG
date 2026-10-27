module

public import CFSG.RankThree.PartOne.N143.O7Basic
import Certificates.Kernel.E27Orth.O73Glue

public section

namespace Certificates

open CFSG.RankThree.PartOne.N143.O7 in
theorem certificate131009 : ∃ S : Subgroup ↥Om, Nat.card S = 3 ^ 9 ∧
    ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ Subgroup.centralizer ({s} : Set ↥Om)) :=
  CertificateChecks.KernelE27Orth.O73.o73131009_fact

end Certificates
