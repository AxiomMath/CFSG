module

public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaA8Data
import CFSG.Certificates.Kernel.A8HoldSound
import Certificates.Kernel.A8Hold.Check
public import Mathlib.GroupTheory.Perm.Sign

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec21.Holder214Theta in
theorem certificate799101 :
    (∀ π : Equiv.Perm (Fin 8), π * a8C1 = a8C1 * π → π * a8C2 = a8C2 * π → π ^ 2 = 1 →
        π = 1 ∨ π = a8Tau) ∧
    ∀ p : Equiv.Perm (Fin 8), Equiv.Perm.sign p = 1 → p * a8Tau = a8Tau * p → p ≠ 1 →
      p ^ 128 = 1 → (p * a8C2 * p⁻¹ * a8C2⁻¹) ^ 128 ≠ 1 ∨
        (p * (a8C1 * a8C2) * p⁻¹ * (a8C1 * a8C2)⁻¹) ^ 128 ≠ 1 :=
  ⟨CFSG.KC.A8Hold.a8_invol_of KernelA8Hold.a8Chk1_ok,
    CFSG.KC.A8Hold.a8_two_of KernelA8Hold.a8Chk2_ok⟩

end Certificates
