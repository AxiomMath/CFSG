module

public import Certificates.Certificate260394

public section

namespace CFSG.Quasithin.B45Exc.Ru

open CFSG.Quasithin.B45Exc.Tab CFSG.Sporadic.RuSchreier

theorem ru_syl_checks :
    ∀ B : Subgroup (Equiv.Perm (Fin 4060)), B ≤ ruS → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → (∀ x ∈ B, x ≠ 1 → (fixFinset x).card = 92) →
      Nat.card B ≤ 2 ^ 6 ∧ (Nat.card B = 2 ^ 5 ∨ Nat.card B = 2 ^ 6 →
        ∃ x₁ ∈ B, ∃ x₂ ∈ B, ∃ x₃ ∈ B, ∃ x₄ ∈ B, ∃ G ∈ ruP,
          (x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹)) ^ 29 = 1 ∧
            x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹) ≠ 1) :=
  Certificates.certificate260394


theorem ru_syl_card_le (B : Subgroup (Equiv.Perm (Fin 4060))) (hBS : B ≤ ruS)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (h2A : ∀ x ∈ B, x ≠ 1 → (fixFinset x).card = 92) : Nat.card B ≤ 2 ^ 6 :=
  (ru_syl_checks B hBS hcomm hsq h2A).1

theorem ru_syl_dbl (B : Subgroup (Equiv.Perm (Fin 4060))) (hBS : B ≤ ruS)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (h2A : ∀ x ∈ B, x ≠ 1 → (fixFinset x).card = 92)
    (hcard : Nat.card B = 2 ^ 5 ∨ Nat.card B = 2 ^ 6) :
    ∃ x₁ ∈ B, ∃ x₂ ∈ B, ∃ x₃ ∈ B, ∃ x₄ ∈ B, ∃ G ∈ ruP,
      (x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹)) ^ 29 = 1 ∧
        x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹) ≠ 1 :=
  (ru_syl_checks B hBS hcomm hsq h2A).2 hcard

end CFSG.Quasithin.B45Exc.Ru
