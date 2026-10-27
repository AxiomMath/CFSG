module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

structure OrthMinusData {V : Type} [CommGroup V] (D : Subgroup (MulAut V)) (I : Subgroup V)
    (a : ℕ) : Prop where
  one_le : 1 ≤ a
  card : Nat.card ↥I = 2 ^ (4 * a)
  psl : IsPSL 2 2 (2 * a) ↥D
  free : ∀ j ∈ D, j ≠ 1 → j * j = 1 →
    Nat.card ↥(I ⊓ fixV (Subgroup.zpowers j)) ^ 2 = Nat.card ↥I
  scalars : ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (_ : Module F₀ (Additive ↥I)),
    Nat.card F₀ = 2 ^ a ∧
      ∀ g ∈ autSub D I, ∀ (c : F₀) (v : Additive ↥I),
        Additive.ofMul (g (Additive.toMul (c • v))) = c • Additive.ofMul (g (Additive.toMul v))

end CFSG.Quasithin
