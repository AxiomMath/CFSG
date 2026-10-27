module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.F918Z4c1
public import CFSG.Sporadic.J1

public section

namespace CFSG.Quasithin

theorem orderOf_two_zmod_nineteen : orderOf (2 : ZMod 19) = 18 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

theorem eighteen_le_of_j1 {L : Type} [Group L] [Finite L]
    (hL : IsSporadic .J1 L) {F : Type} [Field F] [Finite F] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) : 18 ≤ d * e := by
  obtain ⟨φ⟩ := hL
  have hcard : Nat.card L = 175560 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  have h19 : 19 ∣ Nat.card L := by rw [hcard]; norm_num
  have h := orderOf_two_le_of_prime_dvd_card hF ρ hρ (by norm_num : Nat.Prime 19) (by norm_num) h19
  rwa [orderOf_two_zmod_nineteen] at h

end CFSG.Quasithin
