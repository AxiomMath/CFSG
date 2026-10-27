module

public import Certificates.Certificate7104

public section

namespace CFSG.Quasithin.H13.H9Four

open CFSG.Open CFSG.Quasithin.E3

theorem model_card_le {A : Subgroup (MulAut Pt)}
    (hAM : A ≤ modelM4) (hA : IsElemAbelian2 A) : Nat.card A ≤ 2 ^ 4 :=
  Certificates.certificate7104.1 A hAM hA

theorem model_le_L {A : Subgroup (MulAut Pt)}
    (hAM : A ≤ modelM4) (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hff : Nat.card Pt ≤ Nat.card A * Nat.card (fixV A)) : A ≤ modelL4 :=
  (Certificates.certificate7104.2.1 A hAM hA hA1 hff).1

theorem model_card_eq_of_ff {A : Subgroup (MulAut Pt)}
    (hAM : A ≤ modelM4) (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hff : Nat.card Pt ≤ Nat.card A * Nat.card (fixV A)) : Nat.card A = 2 ^ 4 :=
  (Certificates.certificate7104.2.1 A hAM hA hA1 hff).2

theorem model_lemH93 : ∃ A₀ A₁ A₂ : Subgroup (MulAut Pt),
    (∀ A ∈ ({A₀, A₁, A₂} : Set (Subgroup (MulAut Pt))),
      A ≤ modelM4 ∧ IsElemAbelian2 A ∧ Nat.card A = 2 ^ 4) ∧
    (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → Nat.card A = 2 ^ 4 →
      ∃ m ∈ modelM4, A = conjAut A₀ m ∨ A = conjAut A₁ m ∨ A = conjAut A₂ m) ∧
    (Nat.card (fixV A₀) = 2 ^ 4 ∧ gammaCheck 2 A₀ = ⊤) ∧
    (Nat.card (fixV A₁) = 2 ∧ Nat.card (gammaCheck 2 A₁) = 2 ^ 6) ∧
    (Nat.card (fixV A₂) = 2 ^ 2 ∧ Nat.card (gammaCheck 2 A₂) = 2 ^ 6 ∧
      ∀ a ∈ A₂, (∀ w ∈ gammaCheck 2 A₂, a w = w) → a = 1) ∧
    ∀ A ∈ ({A₁, A₂} : Set (Subgroup (MulAut Pt))),
      (∃ b ∈ A ⊓ modelL4, IsTransvOn b ptW₁) ∧
        (∃ b ∈ A ⊓ modelL4, b ≠ 1 ∧ ¬ IsTransvOn b ptW₁) ∧
        2 ^ 7 ≤ Nat.card (gammaCheck 3 A) :=
  Certificates.certificate7104.2.2.2.2.2

end CFSG.Quasithin.H13.H9Four
