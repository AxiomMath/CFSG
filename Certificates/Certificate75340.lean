module

public import CFSG.Sporadic.Fi23.Classes
import Certificates.Kernel.Fi23B0.Group

public section

namespace Certificates

open CertificateChecks

theorem certificate75340 : ∃ B : Subgroup CFSG.Sporadic.Fi23.J,
    CFSG.Sporadic.Fi23.slvl 0 ≤ B ∧
    CFSG.Sporadic.Fi23.slvl 0 ≤
      Subgroup.centralizer ({CFSG.Sporadic.Fi23.conjPt 2776} : Set CFSG.Sporadic.Fi23.J) ∧
    Nat.card B = 318504960 ∧
    ¬ B ≤ Subgroup.centralizer ({CFSG.Sporadic.Fi23.conjPt 2776} : Set CFSG.Sporadic.Fi23.J) := KernelFi23B0.b0_exists

end Certificates
