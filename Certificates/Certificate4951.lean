module

public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.KFU

open Equiv

private theorem cert4951_perm_four_conj_two : ∀ t₁ t₂ : Perm (Fin 4),
    (t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₂ * t₂ = 1 ∧ t₂ ≠ 1 ∧ (t₁ * t₂) ^ 3 = 1 ∧ t₁ * t₂ ≠ 1) →
      ∃ π : Perm (Fin 4), π * swap 0 1 * π⁻¹ = t₁ ∧ π * swap 1 2 * π⁻¹ = t₂ := by
  decide +kernel

private theorem cert4951_perm_five_conj_two : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    (swap a b * swap c d) ^ 3 = 1 → swap a b * swap c d ≠ 1 →
      ∃ π : Perm (Fin 5), π * swap 0 1 * π⁻¹ = swap a b ∧ π * swap 1 2 * π⁻¹ = swap c d := by
  decide +kernel

private theorem cert4951_perm_five_conj_three : ∀ a b c d e f : Fin 5,
    (a ≠ b ∧ c ≠ d ∧ e ≠ f ∧ (swap a b * swap c d) ^ 3 = 1 ∧ swap a b * swap c d ≠ 1 ∧
    (swap c d * swap e f) ^ 3 = 1 ∧ swap c d * swap e f ≠ 1 ∧
    (swap a b * swap e f) ^ 2 = 1 ∧ swap a b * swap e f ≠ 1) →
      ∃ π : Perm (Fin 5), π * swap 0 1 * π⁻¹ = swap a b ∧ π * swap 1 2 * π⁻¹ = swap c d ∧
        π * swap 2 3 * π⁻¹ = swap e f := by
  decide +kernel

private theorem cert4951_perm_five_conj_four : ∀ (π : Perm (Fin 5)) (g h : Fin 5),
    (g ≠ h ∧ (π * swap 2 3 * π⁻¹ * swap g h) ^ 3 = 1 ∧ π * swap 2 3 * π⁻¹ * swap g h ≠ 1 ∧
    (π * swap 0 1 * π⁻¹ * swap g h) ^ 2 = 1 ∧ π * swap 0 1 * π⁻¹ * swap g h ≠ 1 ∧
    (π * swap 1 2 * π⁻¹ * swap g h) ^ 2 = 1 ∧ π * swap 1 2 * π⁻¹ * swap g h ≠ 1) →
      swap g h = π * swap 3 4 * π⁻¹ := by
  decide +kernel

private theorem cert4951_perm_five_cycle : ∀ π : Perm (Fin 5), π ^ 5 = 1 → π = 1 ∨
    ∃ a, π a ≠ a ∧ π (π a) ≠ a ∧ π (π (π a)) ≠ a := by
  decide +kernel

end CFSG.RankThree.PartOne.KFU

namespace Certificates

open Equiv in
theorem certificate4951 : (
    ∀ t₁ t₂ : Perm (Fin 4),
      (t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₂ * t₂ = 1 ∧ t₂ ≠ 1 ∧ (t₁ * t₂) ^ 3 = 1 ∧ t₁ * t₂ ≠ 1) →
        ∃ π : Perm (Fin 4), π * swap 0 1 * π⁻¹ = t₁ ∧ π * swap 1 2 * π⁻¹ = t₂
  ) ∧ (
    ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
      (swap a b * swap c d) ^ 3 = 1 → swap a b * swap c d ≠ 1 →
        ∃ π : Perm (Fin 5), π * swap 0 1 * π⁻¹ = swap a b ∧ π * swap 1 2 * π⁻¹ = swap c d
  ) ∧ (
    ∀ a b c d e f : Fin 5,
      (a ≠ b ∧ c ≠ d ∧ e ≠ f ∧ (swap a b * swap c d) ^ 3 = 1 ∧ swap a b * swap c d ≠ 1 ∧
      (swap c d * swap e f) ^ 3 = 1 ∧ swap c d * swap e f ≠ 1 ∧
      (swap a b * swap e f) ^ 2 = 1 ∧ swap a b * swap e f ≠ 1) →
        ∃ π : Perm (Fin 5), π * swap 0 1 * π⁻¹ = swap a b ∧ π * swap 1 2 * π⁻¹ = swap c d ∧
          π * swap 2 3 * π⁻¹ = swap e f
  ) ∧ (
    ∀ (π : Perm (Fin 5)) (g h : Fin 5),
      (g ≠ h ∧ (π * swap 2 3 * π⁻¹ * swap g h) ^ 3 = 1 ∧ π * swap 2 3 * π⁻¹ * swap g h ≠ 1 ∧
      (π * swap 0 1 * π⁻¹ * swap g h) ^ 2 = 1 ∧ π * swap 0 1 * π⁻¹ * swap g h ≠ 1 ∧
      (π * swap 1 2 * π⁻¹ * swap g h) ^ 2 = 1 ∧ π * swap 1 2 * π⁻¹ * swap g h ≠ 1) →
        swap g h = π * swap 3 4 * π⁻¹
  ) ∧ (
    ∀ π : Perm (Fin 5), π ^ 5 = 1 → π = 1 ∨
      ∃ a, π a ≠ a ∧ π (π a) ≠ a ∧ π (π (π a)) ≠ a
  ) :=
  ⟨CFSG.RankThree.PartOne.KFU.cert4951_perm_four_conj_two,
    CFSG.RankThree.PartOne.KFU.cert4951_perm_five_conj_two,
    CFSG.RankThree.PartOne.KFU.cert4951_perm_five_conj_three,
    CFSG.RankThree.PartOne.KFU.cert4951_perm_five_conj_four,
    CFSG.RankThree.PartOne.KFU.cert4951_perm_five_cycle⟩

end Certificates
