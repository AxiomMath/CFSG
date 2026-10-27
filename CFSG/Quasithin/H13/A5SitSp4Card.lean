module

public import CFSG.Quasithin.H13.A5SitSp4

public section

namespace CFSG.Quasithin.H13.A5.Orth

theorem card_SC : Fintype.card SC = 720 := by
  decide +kernel

theorem card_Spq : Nat.card Spq = 720 := by
  rw [← card_SC, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.ofBijective _ ⟨toSC_injective, toSC_surjective⟩)

end CFSG.Quasithin.H13.A5.Orth
