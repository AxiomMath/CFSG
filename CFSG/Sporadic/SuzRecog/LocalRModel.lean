module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup

variable {H : Type*} [Group H]

@[expose] def locC (l : H) (T : Subgroup H) : Subgroup H :=
  centralizer ({l} : Set H) ⊓ centralizer (T : Set H)

structure LocModel (l : H) (T : Subgroup H) : Prop where
  card_V : Nat.card (centralizer ({l} : Set H)) = 512
  T_le : T ≤ centralizer ({l} : Set H)
  card_T : Nat.card T = 64
  mem_T : ∀ u ∈ centralizer ({l} : Set H), orderOf u = 2 → ¬ IsConj u l → u ∈ T
  card_C : Nat.card (locC l T) = 16
  act_C : ∀ x ∈ centralizer ({l} : Set H), x ∉ T ⊔ locC l T →
    ∃ c ∈ locC l T, x * c * x⁻¹ * c⁻¹ ∉ T
  exists_inv : ∃ x ∈ centralizer ({l} : Set H), x ∉ T ⊔ locC l T ∧ x * x = 1
  swap : ∀ x ∈ centralizer ({l} : Set H), x ∉ T ⊔ locC l T →
    ∃ e ∈ T, e * e = 1 ∧ e * (x * e * x⁻¹) ≠ x * e * x⁻¹ * e
  rho : ∀ u ∈ locC l T, u * u = 1 → u ≠ 1 → u ≠ l → u ∉ T → l * u ∉ T →
    ∀ c : H, Odd (orderOf c) → (c * l * c⁻¹ = u ∨ c * l * c⁻¹ = l * u) →
      (c * u * c⁻¹ = l ∨ c * u * c⁻¹ = u ∨ c * u * c⁻¹ = l * u) → c ∈ centralizer (T : Set H)
  card_cent_T : Nat.card (centralizer (T : Set H)) = 192

end CFSG.Sporadic.SuzRecog.LocalR
