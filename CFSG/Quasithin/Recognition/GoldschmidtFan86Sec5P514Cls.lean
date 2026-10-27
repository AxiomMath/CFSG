module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Quasithin.Fan86

namespace P514

theorem cls_int (r o : ℤ) (_hr : 3 ≤ r) (hodd : r % 2 = 1)
    (tL₁ tR₁ a₁ b₁ tL₂ tR₂ a₂ b₂ : ℤ)
    (hf₁ : tL₁ ≤ o - r ∧ o + r ≤ tR₁) (hf₂ : tL₂ ≤ o - r ∧ o + r ≤ tR₂)
    (hc₁ : (a₁ = o ∧ b₁ = o + 1) ∨ (a₁ = o ∧ b₁ = o + 2))
    (hc₂ : (a₂ = o ∧ b₂ = o + 1) ∨ (a₂ = o ∧ b₂ = o + 2))
    (hc3₁ : -1 ≤ (tR₁ - b₁) - r ∧ (tR₁ - b₁) - r ≤ 1 ∧ -1 ≤ (a₁ - tL₁) - r ∧
      (a₁ - tL₁) - r ≤ 1 ∧ -1 ≤ (tR₁ - b₁) - (a₁ - tL₁) ∧ (tR₁ - b₁) - (a₁ - tL₁) ≤ 1)
    (hc3₂ : -1 ≤ (tR₂ - b₂) - r ∧ (tR₂ - b₂) - r ≤ 1 ∧ -1 ≤ (a₂ - tL₂) - r ∧
      (a₂ - tL₂) - r ≤ 1 ∧ -1 ≤ (tR₂ - b₂) - (a₂ - tL₂) ∧ (tR₂ - b₂) - (a₂ - tL₂) ≤ 1)
    (m₁ i₁ j₁ : ℤ) (hp₁ : (i₁ = 0 ∨ i₁ = 1) ∧ (j₁ = 0 ∨ j₁ = 1) ∧ tR₁ = a₁ + 2 * m₁ - i₁ ∧
      tL₁ + 2 * m₁ = b₁ + j₁)
    (m₂ i₂ j₂ : ℤ) (hp₂ : (i₂ = 0 ∨ i₂ = 1) ∧ (j₂ = 0 ∨ j₂ = 1) ∧ tR₂ = a₂ + 2 * m₂ - i₂ ∧
      tL₂ + 2 * m₂ = b₂ + j₂)
    (hR : (tR₁ < tR₂ → tR₁ = o + r + 2) ∧ (tR₂ < tR₁ → tR₂ = o + r + 2) ∧
      (tR₁ = tR₂ → tR₁ + 1 ≤ o + r + 2))
    (hL : (tL₂ < tL₁ → tL₁ = o - r) ∧ (tL₁ < tL₂ → tL₂ = o - r) ∧
      (tL₁ = tL₂ → o - r ≤ tL₁ - 1)) :
    ((tR₁ = o + r + 3 ∧ b₁ = o + 2) ∨ (tR₂ = o + r + 3 ∧ b₂ = o + 2)) ∧
    ((tL₁ = o - r - 1 ∧ a₁ = o) ∨ (tL₂ = o - r - 1 ∧ a₂ = o)) := by
  obtain ⟨hf₁l, hf₁r⟩ := hf₁
  obtain ⟨hf₂l, hf₂r⟩ := hf₂
  obtain ⟨hi₁, hj₁, hp₁a, hp₁b⟩ := hp₁
  obtain ⟨hi₂, hj₂, hp₂a, hp₂b⟩ := hp₂
  obtain ⟨hR1, hR2, hR3⟩ := hR
  obtain ⟨hL1, hL2, hL3⟩ := hL
  rcases hc₁ with ⟨ha₁, hb₁⟩ | ⟨ha₁, hb₁⟩ <;> rcases hc₂ with ⟨ha₂, hb₂⟩ | ⟨ha₂, hb₂⟩ <;>
    rcases hi₁ with rfl | rfl <;> rcases hj₁ with rfl | rfl <;>
    rcases hi₂ with rfl | rfl <;> rcases hj₂ with rfl | rfl <;> omega

end P514

end CFSG.Quasithin.Fan86
