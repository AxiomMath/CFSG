module

public import Certificates.Certificate10506

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2

section Main


theorem t24_facts : Nat.card t24 = 2 ^ 10 ∧ (∀ t ∈ t24, rho t (toVecD 11 3) = toVecD 11 3) ∧
    ∀ K : Subgroup PM24, K ≤ t24 → K ≠ ⊥ → (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) →
      (∀ x ∈ K, x * x = 1) →
      Nat.card K * Nat.card {v : Fin 11 → ZMod 2 // ∀ p ∈ K, rho p v = v} ≤ 2 ^ 10 :=
  Certificates.certificate10506

theorem card_t24 : Nat.card t24 = 2 ^ 10 := t24_facts.1

theorem rho_t24_xA {t : PM24} (ht : t ∈ t24) : rho t (toVecD 11 3) = toVecD 11 3 :=
  t24_facts.2.1 t ht

theorem card_mul_card_fixed_le {K : Subgroup PM24} (hKT : K ≤ t24) (hK : K ≠ ⊥)
    (hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hsq : ∀ x ∈ K, x * x = 1) :
    Nat.card K * Nat.card {v : Fin 11 → ZMod 2 // ∀ p ∈ K, rho p v = v} ≤ 2 ^ 10 :=
  t24_facts.2.2 K hKT hK hcomm hsq

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
