module

public import CFSG.CGT.Hall82.DModelFacts
import Certificates.Certificate15060
import Certificates.Kernel.Hall82K.Facts

public section

namespace Certificates

open CFSG.KC.Hall82K

open CFSG.CGT.Hall82 CFSG.ComponentClassification.AS81.Hexa in
theorem certificate840004 :
    (∀ a : Fin 3 → Fin 64,
      (∀ i j, hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = 1 ∨
        hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = transl 5) →
      (∀ i, hallXi a i * hallXi a i = 1 ∨ hallXi a i * hallXi a i = transl 5) →
      (∀ s ∈ hexaM, s 5 = 5 → ∀ i, ∃ u, InHallU u ∧ ∃ e, s * hallXi a i * s⁻¹ =
        transl u * hallXProd a e) →
      ∀ i, InHallU (a i)) ∧
    (∀ x ∈ hallX1, ∀ y ∈ hallX1, xcode (x * y) = xorF (xcode x) (xcode y)) ∧
    (∀ x ∈ hallX1, xcode x = 0 ↔ x = 1 ∨ x = transl 5) ∧
    (∀ k, ∃ x ∈ hallX1, xcode x = k) ∧
    (∀ x ∈ hallX1, x * x = transl 5 ↔ hallQ0 (xcode x) = true) ∧
    (∀ x ∈ hallX1, IsHallOrb (xcode x) → ∃ h, IsOvalVec h ∧ x = transl h) ∧
    (∀ b, ∀ s ∈ hexaM, s 5 = 5 → ∃ σ ∈ hallS40, ∀ x ∈ hallX1,
      xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x)) ∧
    (∀ σ ∈ hallS40, ∃ b, ∃ s ∈ hexaM, s 5 = 5 ∧ ∀ x ∈ hallX1,
      xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x)) ∧
    (∀ y : Fin 64 → Fin 64, (∀ k l, y (xorF k l) = xorF (y k) (y l)) →
      (∀ k, hallQ0 (y k) = hallQ0 k) → (∀ k, y k = 0 → k = 0) → GoodHall y →
      (∀ t ∈ hallS40, GoodHall (y ∘ t ∘ y)) →
      (∀ t ∈ hallS40, ∀ u ∈ hallS40, GoodHall (y ∘ t ∘ y ∘ u ∘ y)) →
      ∀ k, InHallW k → InHallW (y k)) :=
  ⟨lift_k, xcode_mul_k, xcode_eq_zero_k, xcode_surj_k, xcode_sq_k, xcode_orb_k,
    xcode_conj_k certificate15052, xcode_conj_surj_k certificate15052
      certificate15060, reducible_k⟩

end Certificates
