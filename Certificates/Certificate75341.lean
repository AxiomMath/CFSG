module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporMcLZ2
import Certificates.Kernel.Asch54.McLGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.McLProof CFSG.LocalAnalysis.WeakClosure81.SporMcL Subgroup in
theorem certificate75341 : pa ∈ S ∧ (∀ x ∈ S, (∀ t ∈ S, x * t = t * x) → x = 1 ∨ x = pa) ∧
    Nat.card ↥(P ⊓ normalizer z2Set) = 1152 ∧ P ≤ K ⊔ (P ⊓ normalizer z2Set) := KernelSpor.McLAsch.mcl_facts

end Certificates
