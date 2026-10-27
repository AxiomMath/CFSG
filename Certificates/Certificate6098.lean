module

public import CFSG.Sporadic.HN.LocalK
import Certificates.Kernel.HNLocal.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK in
theorem certificate6098 : wG 12 ^ 2 = 1 ∧ wG 13 ^ 2 = 1 ∧ wG 12 ≠ 1 ∧ wG 13 ≠ 1 ∧
    (mat dHN (wG 12)).trace ≠ (mat dHN (wG 13)).trace ∧
    ∃ Q : Subgroup (J dHN), Nat.card Q = 2 ^ 14 ∧ ∀ g ∈ Q, g ^ 2 = 1 → g ≠ 1 →
      ∃ (i : Fin 2) (h : J dHN) (m : ℕ), m % 2 = 1 ∧ (g * (h * wG (12 + i.val) * h⁻¹)) ^ m = 1 := KernelHNLocal.facts6098

end Certificates
