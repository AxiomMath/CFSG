module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1U0
import Certificates.Kernel.PermCent.U43QuatFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43ModelBase

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M in
open CFSG.EvenSporadicStandard.M24Std.CU43 (P tP) in
theorem certificate55122 : (∀ g ∈ P, ∀ k < 8, CfgCore (g * tP k) → ∃ c ∈ gamP, g * tP k = c * d2P * c⁻¹) ∧
    Nat.card ↥(P ⊓ Subgroup.centralizer ({d2P} : Set (Equiv.Perm (Fin 820)))) = 6048 := KernelPermCent.U43Quat.facts55122

end Certificates
