module

public import CFSG.Sporadic.J4

public section

namespace CFSG.Quasithin.H13

open CFSG.Blueprint

@[expose] def J4SevenNotReal : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier .J4) →
    ∀ x g : X, orderOf x = 7 → g * x * g⁻¹ ≠ x⁻¹

theorem card_not_dvd_forty_nine {X : Type} [Group X]
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .J4)) : ¬ 49 ∣ Nat.card X := by
  obtain ⟨e⟩ := hX
  have hc : Nat.card X = 86775571046077562880 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  rw [hc]
  decide

end CFSG.Quasithin.H13
