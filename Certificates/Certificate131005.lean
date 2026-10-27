module

import Certificates.Kernel.E27Orth.O10mGlue
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace Certificates

open Subgroup CFSG.Assembly.LowTwoRank in
theorem certificate131005 :
    ∃ S : Subgroup ↥(StatedOmega (StatedQuadMinus 5 (ZMod 2) 1 1)), Nat.card S = 729 ∧
      ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ centralizer
        ({s} : Set ↥(StatedOmega (StatedQuadMinus 5 (ZMod 2) 1 1)))) :=
  CertificateChecks.KernelE27Orth.O10m.o10m131005_fact

end Certificates
