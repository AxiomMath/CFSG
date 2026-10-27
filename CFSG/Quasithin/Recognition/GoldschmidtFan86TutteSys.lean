module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H]

@[expose] def tx (r l : H) (i : ℤ) : H := l ^ (-i) * r ^ i

structure IsTutteSys (s : ℕ) (r l ξ : H) (Hs : ℕ → Subgroup H) : Prop where
  one_le : 1 ≤ s
  zero : Hs 0 = ⊥
  mono : ∀ i, i < s → Hs i ≤ Hs (i + 1)
  card_lt : ∀ i, i < s → Nat.card (Hs i) = 2 ^ i
  card_s : Nat.card (Hs s) = 3 * 2 ^ (s - 1)
  x_mem : ∀ i : ℕ, i ≤ s → tx r l i ∈ Hs i
  x_not_mem : ∀ i : ℕ, 1 ≤ i → i ≤ s → tx r l i ∉ Hs (i - 1)
  xs_sq_not_mem : tx r l s ^ 2 ∉ Hs (s - 1)
  xs_cube_mem : tx r l s ^ 3 ∈ Hs (s - 1)
  xi_sq : ξ * ξ = 1
  xi_case : (ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹) ∨ (ξ * r * ξ = l⁻¹ ∧ ξ * l * ξ = r⁻¹)
  rel : ξ * r ^ s * tx r l s ∈ Hs (s - 1)
  inter : ∀ i, i ≤ s → Hs (s - i) ⊓ (Hs i).map (MulAut.conj ξ).toMonoidHom = ⊥

@[expose] def TutteCalculus : Prop :=
  ∀ (H : Type) [Group H] (s : ℕ) (r l ξ : H) (Hs : ℕ → Subgroup H),
    IsTutteSys s r l ξ Hs → s ≤ 5

end CFSG.Quasithin.Fan86.Tutte
