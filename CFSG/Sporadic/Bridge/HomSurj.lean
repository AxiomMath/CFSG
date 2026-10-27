module

public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.Sporadic.Bridge

theorem nonempty_mulEquiv_of_le_range {P N : Type*} [Group P] [Group N] [Finite P]
    {H : Subgroup N} (φ : P →* N) (hH : H ≤ φ.range) {k : ℕ} (hP : Nat.card P ≤ k)
    (hk : k ≤ Nat.card H) : Nonempty (H ≃* P) := by
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have hle : Nat.card φ.range ≤ Nat.card H :=
    (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective).trans (hP.trans hk)
  obtain rfl := Subgroup.eq_of_le_of_card_ge hH hle
  exact nonempty_mulEquiv_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective hP hk

end CFSG.Sporadic.Bridge
