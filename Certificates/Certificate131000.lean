module

public import CFSG.Sporadic.Schreier.Co3Cert
import Certificates.Kernel.E27Lie.Co3Facts
import CFSG.Sporadic.Schreier.Co3Arrays
import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
meta import CFSG.Sporadic.Schreier.Co3Cert
meta import Certificates.Data.CFSGNative.Schreier.Check
public import Mathlib.GroupTheory.Schreier

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Co3 in
theorem certificate131000 : ∃ S : Subgroup ↥co3P, Nat.card S = 3 ^ (Nat.card ↥co3P).factorization 3 ∧
    ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ Subgroup.centralizer ({s} : Set ↥co3P)) := KernelE27Lie.Co3.co3_sylow

end Certificates
