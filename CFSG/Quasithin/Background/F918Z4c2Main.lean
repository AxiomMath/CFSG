module

public import CFSG.Quasithin.Background.F918Z4c2TI
public import CFSG.Quasithin.Background.F918Z4c2Real
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.Quasithin.Z4c2

open CFSG.Quasithin CFSG.Timmesfeld

theorem torus_bound_of_isPSL_two_two {L : Type} [Group L] [Finite L] {n : ℕ} (hL : IsPSL 2 2 n L)
    {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrL : r ∣ Nat.card L) :
    orderOf ((Nat.card F : ℕ) : ZMod r) ≤ d ∧
      (Odd (orderOf ((Nat.card F : ℕ) : ZMod r)) →
        2 * orderOf ((Nat.card F : ℕ) : ZMod r) ≤ d) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrL
  obtain ⟨w, hw⟩ := exists_inverting hL x
  refine torus_inversion_bound hr hr2 (ρ x) ?_ ?_ ⟨ρ w, ?_⟩
  · rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  · intro h
    have hx1 : x = 1 := hρ (by rw [h, map_one])
    rw [hx1, orderOf_one] at hx
    exact hr.one_lt.ne hx
  · rw [← map_inv, ← map_mul, ← map_mul, hw, map_inv]

theorem two_pow_zmod_seven (e : ℕ) : ((2 ^ e : ℕ) : ZMod 7) = 2 ^ (e % 3) := by
  have h8 : (2 : ZMod 7) ^ 3 = 1 := by decide
  rw [Nat.cast_pow, Nat.cast_ofNat]
  conv_lhs => rw [← Nat.div_add_mod e 3, pow_add, pow_mul, h8, one_pow, one_mul]

theorem orderOf_two_pow_zmod_seven_of_dvd {e : ℕ} (h : 3 ∣ e) :
    orderOf (((2 ^ e : ℕ)) : ZMod 7) = 1 := by
  rw [two_pow_zmod_seven, Nat.mod_eq_zero_of_dvd h]
  simp

theorem orderOf_two_pow_zmod_seven_of_not_dvd {e : ℕ} (h : ¬ 3 ∣ e) :
    orderOf (((2 ^ e : ℕ)) : ZMod 7) = 3 := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [two_pow_zmod_seven]
  have h3 : e % 3 = 1 ∨ e % 3 = 2 := by omega
  rcases h3 with h3 | h3 <;> rw [h3] <;> exact orderOf_eq_prime (by decide) (by decide)

theorem six_le_of_psl2_eight {L : Type} [Group L] [Finite L] (hL : IsPSL 2 2 3 L) {F : Type}
    [Field F] [Finite F] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) : 6 ≤ d * e := by
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  have h7 : 7 ∣ Nat.card L := by
    rw [card_of_isPSL_two_two hL]
    norm_num
  obtain ⟨hk1, hk2⟩ := torus_bound_of_isPSL_two_two hL ρ hρ (r := 7) (by norm_num) (by norm_num) h7
  rw [hF] at hk1 hk2
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · have := Finite.one_lt_card (α := F)
      rw [hF, h] at this
      simp at this
    · exact h
  by_cases h3 : 3 ∣ e
  · rw [orderOf_two_pow_zmod_seven_of_dvd h3] at hk2
    have hd2 : 2 * 1 ≤ d := hk2 (by decide)
    obtain ⟨m, rfl⟩ := h3
    have : 1 ≤ m := by omega
    nlinarith
  · rw [orderOf_two_pow_zmod_seven_of_not_dvd h3] at hk2
    have hd6 : 2 * 3 ≤ d := hk2 (by decide)
    nlinarith

theorem sq_eq_one_of_orderOf_bound {r : ℕ} (hr : r.Prime) {u : ZMod r} (hu : u ≠ 0)
    (h1 : orderOf u ≤ 3) (h2 : Odd (orderOf u) → 2 * orderOf u ≤ 3) : u ^ 2 = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hpos : 0 < orderOf u :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨r - 1, by have := hr.one_lt; omega, ZMod.pow_card_sub_one_eq_one hu⟩)
  have hne3 : orderOf u ≠ 3 := fun h => by
    have := h2 (by rw [h]; decide)
    omega
  have hk : orderOf u = 1 ∨ orderOf u = 2 := by omega
  rcases hk with hk | hk
  · rw [orderOf_eq_one_iff.mp hk]
    simp
  · rw [← hk]
    exact pow_orderOf_eq_one u

theorem not_faithful_three {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 2 2 n L) {F : Type} [Field F] [Finite F] {e : ℕ} (hF : Nat.card F = 2 ^ e)
    (he : 3 * e < 2 * n + 2) (ρ : L →* Matrix.GeneralLinearGroup (Fin 3) F)
    (hρ : Function.Injective ρ) : False := by
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · have := Finite.one_lt_card (α := F)
      rw [hF, h] at this
      simp at this
    · exact h
  have key : ∀ r k₀ : ℕ, IsPrimitivePrimeDivisor r k₀ → 0 < k₀ → r ∣ Nat.card L → k₀ ∣ 2 * e := by
    intro r k₀ hr hk₀ hrL
    have hr2 : r ≠ 2 := hr.ne_two hk₀
    obtain ⟨hk1, hk2⟩ := torus_bound_of_isPSL_two_two hL ρ hρ hr.prime hr2 hrL
    have hu : ((Nat.card F : ℕ) : ZMod r) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff, hF]
      intro h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp
        (hr.prime.dvd_of_dvd_pow h))
    have hsq := sq_eq_one_of_orderOf_bound hr.prime hu hk1 hk2
    rw [hF, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul] at hsq
    have hdvd : r ∣ 2 ^ (e * 2) - 1 := (Bang.dvd_two_pow_sub_one_iff _).mpr hsq
    have := (hr.dvd_sub_one_iff hk₀ _).mp hdvd
    rwa [mul_comm] at this
  by_cases hn3 : n = 3
  · subst hn3
    have hpp : IsPrimitivePrimeDivisor 7 3 :=
      ⟨by norm_num, by norm_num, by intro j hj hj3; interval_cases j <;> norm_num⟩
    have h7 : 7 ∣ Nat.card L := by
      rw [card_of_isPSL_two_two hL]
      norm_num
    have h3 := key 7 3 hpp (by norm_num) h7
    omega
  · obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
    have hrL : r ∣ Nat.card L := by
      rw [card_of_isPSL_two_two hL]
      refine Dvd.dvd.mul_left ?_ _
      have := hr.dvd
      rwa [show 2 * n = n * 2 by ring, pow_mul] at this
    have h2n := key r (2 * n) ⟨hr.1, hr.2.1, hr.2.2⟩ (by omega) hrL
    have hne : n ∣ e := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h2n
    have := Nat.le_of_dvd (by omega) hne
    omega

end CFSG.Quasithin.Z4c2
