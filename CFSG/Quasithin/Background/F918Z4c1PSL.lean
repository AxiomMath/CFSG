module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.F918Z4c1Ppd
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin

open CFSG.Timmesfeld

theorem card_eq_of_isPSL_two_two {L : Type} [Group L] {n : ℕ} (hL : IsPSL 2 2 n L) :
    Nat.card L = 2 ^ n * (2 ^ (2 * n) - 1) := by
  obtain ⟨⟨-, hn1, -⟩, K, _, _, hK, ⟨φ⟩⟩ := hL
  rw [Nat.card_congr φ.toEquiv, ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  have hodd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  have h21 : 2 * (2 - 1) / 2 = 1 := by norm_num
  rw [hodd, Nat.div_one, Finset.Icc_self, Finset.prod_singleton, h21, pow_one, ← pow_mul,
    mul_comm n 2]

theorem two_mul_le_of_psl2_two {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3)
    (hL : IsPSL 2 2 n L) {F : Type} [Field F] [Finite F] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) :
    2 * n ≤ d * e := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
  have hrL : r ∣ Nat.card L := by
    rw [card_eq_of_isPSL_two_two hL]
    exact hr.dvd.mul_left _
  exact le_of_isPrimitivePrimeDivisor_dvd_card hF ρ hρ hr (by omega) hrL

end CFSG.Quasithin
