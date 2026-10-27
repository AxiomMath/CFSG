module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9FourFacts
import Certificates.Kernel.H9Four.Assembly
import CFSG.Certificates.Kernel.H9Four.Glue

public section

namespace Certificates

open CFSG.Quasithin.H13.H9Four CFSG.KD.H9Four CFSG.KC.H9Four.Sound

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.H9Four CFSG.Open CFSG.Quasithin.E3 in
theorem certificate7104 :
    (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → Nat.card A ≤ 2 ^ 4) ∧
    (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → A ≠ ⊥ →
      Nat.card Pt ≤ Nat.card A * Nat.card (fixV A) → A ≤ modelL4 ∧ Nat.card A = 2 ^ 4) ∧
    (∀ X : Subgroup (MulAut Pt), X ≤ modelM4 → IsElemAbelian2 X →
      Nat.card (commV X) ≤ 2 ^ 2 → Nat.card X ≤ 2) ∧
    (∀ X : Subgroup (MulAut Pt), X ≤ modelM4 → IsElemAbelian2 X →
      Nat.card Pt ≤ 2 ^ 2 * Nat.card (fixV X) → Nat.card X ≤ 2) ∧
    (∀ B : Subgroup (MulAut Pt), B ≤ modelL4 → IsElemAbelian2 B → 2 ^ 2 ≤ Nat.card B →
      (∀ b ∈ B, ∀ c ∈ B, b ≠ 1 → c ≠ 1 →
        fixV (Subgroup.zpowers b) ⊓ ptW₁ = fixV (Subgroup.zpowers c) ⊓ ptW₁ ∧
          fixV (Subgroup.zpowers b) ⊓ ptW₂ = fixV (Subgroup.zpowers c) ⊓ ptW₂) →
      Nat.card B = 2 ^ 2 ∧
        ∀ b ∈ B, b ≠ 1 → Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ ptW₁) = 2 ^ 2) ∧
    ∃ A₀ A₁ A₂ : Subgroup (MulAut Pt),
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
          2 ^ 7 ≤ Nat.card (gammaCheck 3 A) := by
  have hff := ffCheck16_true
  rw [ffCheckOf, List.all_eq_true] at hff
  refine CFSG.Certificates.Kernel.H9Four.certificate7104_of_checks invL_complete invS_complete
    checkInv_true repCheck_true (fun hi _ hy hc hn => closure_fact hi hy hc hn) rankCheck_true
    (fun gs hgs => ?_) commCheck_true centCheck_true axesCheck_true e16Check_true
  have h1 := hff gs hgs
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff, Bool.and_eq_true,
    beq_iff_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

end Certificates
