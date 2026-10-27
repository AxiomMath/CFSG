module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

@[expose] def FactL211Loc12626 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPSL 2 11 1 X →
    (Nat.card X = 660 ∧ IsSimpleGroup X) ∧
    (∀ α : MulAut X, Odd (orderOf α) → α ∈ (MulAut.conj : X →* MulAut X).range) ∧
    (∀ α : MulAut X, α ^ 2 = 1 → (∃ x : X, orderOf x = 3 ∧ α x = x) →
      α ∈ (MulAut.conj : X →* MulAut X).range) ∧
    (∀ k x : X, k ^ 2 = 1 → k ≠ 1 → (orderOf x = 3 ∨ orderOf x = 5) →
      ∃ g : X, (g * k * g⁻¹) * x * (g * k * g⁻¹)⁻¹ = x⁻¹) ∧
    (∀ k : X, k ^ 2 = 1 → k ≠ 1 → ∃ g h : X,
      Subgroup.closure {k, g * k * g⁻¹, h * k * h⁻¹} = ⊤) ∧
    (∀ k x : X, k ^ 2 = 1 → k ≠ 1 → orderOf x = 3 → x * k = k * x →
      ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.centralizer {k} →
        x ∈ Subgroup.normalizer (Y : Set X) → Y ≤ Subgroup.centralizer {x}) ∧
    (∀ k x y : X, k ^ 2 = 1 → k ≠ 1 → orderOf x = 3 → orderOf y = 3 → x * k = k * x →
      y * k = k * y → y ∈ Subgroup.zpowers x)

end CFSG.Quasithin.H13
