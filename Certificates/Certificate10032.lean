module

public import CFSG.Monster.GMS.Griess13.ChecksInputs
import Certificates.Kernel.Griess13.Checks

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.GMS.Griess13.Co1Data in
open scoped Matrix in
theorem certificate10032 :
    (commCheck = true)
    ∧ (cubeCheck = true)
    ∧ (∀ v : Fin 6 → ZMod 3, v ≠ 0 → PR.eq (prIota v) PR.one = false)
    ∧ (nConjCheck = true)
    ∧ (tauCheck = true)
    ∧ (mSCheck = true)
    ∧ (mConjCheck = true)
    ∧ (∀ i : Fin 2, CFSG.Monster.GMS.Griess13.Co1Data.actP i *ᵥ w1 = w1)
    ∧ (rConjCheck = true)
    ∧ (∀ k : Fin 12, ∃ c : ZMod 3, c ≠ 0 ∧ actR k *ᵥ repw k = c • w1)
    ∧ (repw 0 = w1)
    ∧ (w1 ⬝ᵥ v0 = 1)
    ∧ (decCheck = true)
    ∧ (∀ (s : Fin 2) (k : Fin 12) (j : Fin 2), decEps s k j ≤ 1) := KernelG13.facts10032

end Certificates
