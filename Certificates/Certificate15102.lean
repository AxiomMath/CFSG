module

import Certificates.Kernel.GMS78.Coset.Cards102
public import Certificates.Data.GMS78RuPi7Data

public section

namespace Certificates

open CertificateChecks

theorem certificate15102 : Finite (CFSG.CosetTable.PG 7 CFSG.ComponentClassification.GMS78.RuPi7.pi7Rels) ∧
    Nat.card (CFSG.CosetTable.PG 7 CFSG.ComponentClassification.GMS78.RuPi7.pi7Rels) ≤
      145926144000 := KernelGMS78.Coset.card_pi7

end Certificates
