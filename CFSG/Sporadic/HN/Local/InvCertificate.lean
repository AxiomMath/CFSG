module

public import Certificates.Certificate6098

public section

namespace CFSG.Sporadic.HN.Local

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK

theorem inv_certificate :
    wG 12 ^ 2 = 1 ∧ wG 13 ^ 2 = 1 ∧ wG 12 ≠ 1 ∧ wG 13 ≠ 1 ∧
      (mat dHN (wG 12)).trace ≠ (mat dHN (wG 13)).trace ∧
      ∃ Q : Subgroup (J dHN), Nat.card Q = 2 ^ 14 ∧ ∀ g ∈ Q, g ^ 2 = 1 → g ≠ 1 →
        ∃ (i : Fin 2) (h : J dHN) (m : ℕ), m % 2 = 1 ∧ (g * (h * wG (12 + i.val) * h⁻¹)) ^ m = 1 :=
  Certificates.certificate6098

end CFSG.Sporadic.HN.Local
