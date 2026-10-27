module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

namespace SBc15

structure A5Facts (D : Type) [Group D] (A : Subgroup D) : Prop where
  card_A : Nat.card A = 60
  exists_normalizer : ∀ V : Subgroup D, V ≤ A → Nat.card V = 4 →
    ∃ B : Subgroup D, Nat.card B = 12 ∧ (∀ g ∈ B, ∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧
      (∀ g ∈ A, (∀ v ∈ V, g * v * g⁻¹ ∈ V) → g ∈ B) ∧
      (∀ Y : Subgroup D, Y ≤ A → (∀ v ∈ V, ∀ y ∈ Y, v * y * v⁻¹ ∈ Y) → oTwoUpper Y = Y →
        3 ∣ Nat.card Y → Nat.card Y ∣ 12 → Y = B) ∧
      ∀ a ∈ B, orderOf a = 3 → ∀ w ∈ V, ∃ v ∈ V, v * a * v⁻¹ * a⁻¹ = w

end SBc15

end CFSG.Quasithin
