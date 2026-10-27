module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34CentUni

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate33002 : Nat.card ↥(Subgroup.centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ CFSG.ComponentClassification.PSL3Four.R) = 864 ∧
    Group.IsSolvable ↥(Subgroup.centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ CFSG.ComponentClassification.PSL3Four.R) := KernelLC.L34CentUni.cent_r₄_facts

end Certificates
