module

public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.Quasithin.Background.F918Z4c1

public section

namespace CFSG.Quasithin

open CFSG.Timmesfeld

theorem orderOf_two_eq_of_isPrimitivePrimeDivisor {r k : ℕ} (h : IsPrimitivePrimeDivisor r k)
    (hk : 0 < k) : orderOf (2 : ZMod r) = k := by
  have : Fact r.Prime := ⟨h.prime⟩
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((Bang.dvd_two_pow_sub_one_iff k).mp h.dvd))
    ((h.dvd_sub_one_iff hk _).mp ((Bang.dvd_two_pow_sub_one_iff _).mpr (pow_orderOf_eq_one _)))

theorem le_of_isPrimitivePrimeDivisor_dvd_card {L : Type} [Group L] [Finite L] {F : Type}
    [Field F] [Finite F] {e d k r : ℕ} (hF : Nat.card F = 2 ^ e)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ)
    (hr : IsPrimitivePrimeDivisor r k) (hk : 0 < k) (hrL : r ∣ Nat.card L) : k ≤ d * e := by
  have h := orderOf_two_le_of_prime_dvd_card hF ρ hρ hr.prime (hr.ne_two hk) hrL
  rwa [orderOf_two_eq_of_isPrimitivePrimeDivisor hr hk] at h

end CFSG.Quasithin
