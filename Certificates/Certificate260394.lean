module

import Certificates.Kernel.B45.C260394Fin
public import CFSG.Quasithin.Background.SmithB45ExcHSRuWit
public import CFSG.Sporadic.Schreier.RuDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.B45Exc.Tab in
theorem certificate260394 : ∀ B : Subgroup (Equiv.Perm (Fin 4060)), B ≤ ruS → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → (∀ x ∈ B, x ≠ 1 → (fixFinset x).card = 92) →
    Nat.card B ≤ 2 ^ 6 ∧ (Nat.card B = 2 ^ 5 ∨ Nat.card B = 2 ^ 6 →
      ∃ x₁ ∈ B, ∃ x₂ ∈ B, ∃ x₃ ∈ B, ∃ x₄ ∈ B, ∃ G ∈ ruP,
        (x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹)) ^ 29 = 1 ∧
          x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹) ≠ 1) :=
  KernelB45.C260394.ru_syl

end Certificates
