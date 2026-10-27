module

public import CFSG.Quasithin.Background.D2Params
public import Mathlib.Data.Rat.Star

public section

namespace CFSG.Quasithin.SmithD37

variable {V : Type} [CommGroup V] [Finite V]

theorem natCard_eq_two_pow_rk (hV : ∀ v : V, v ^ 2 = 1) : Nat.card V = 2 ^ rk V :=
  card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)

theorem rkIdx_le_of_rAV_le {X A : Subgroup (MulAut V)} (hA : IsA2 X A) {c : ℕ}
    (hr : rAV A ≤ c) : rkIdx (fixV A) ≤ c * rk A := by
  have h1 := hA.rAV_mul
  have h2 : (rkIdx (fixV A) : ℚ) ≤ c * rk A := by
    rw [← h1]
    exact mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)
  exact_mod_cast h2

theorem rkIdx_lt_of_rAV_lt {X A : Subgroup (MulAut V)} (hA : IsA2 X A) {c : ℕ}
    (hr : rAV A < c) : rkIdx (fixV A) < c * rk A := by
  have h1 := hA.rAV_mul
  have hpos : (0 : ℚ) < rk A := by exact_mod_cast hA.rk_pos
  have h2 : (rkIdx (fixV A) : ℚ) < c * rk A := by
    rw [← h1]
    exact mul_lt_mul_of_pos_right hr hpos
  exact_mod_cast h2

theorem card_le_sq_mul_fixV (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsA2 X A) (hr : rAV A ≤ 2) : Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A) := by
  have h1 := rkIdx_le_of_rAV_le hA (c := 2) (by exact_mod_cast hr)
  rw [natCard_eq_two_pow_rk hV, card_eq_two_pow_of_isPGroup hA.2.2.isPGroup,
    card_eq_two_pow hV, ← pow_mul, ← pow_add, ← rk_add_rkIdx (fixV A)]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_lt_sq_mul_fixV (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsA2 X A) (hr : rAV A < 2) : Nat.card V < Nat.card A ^ 2 * Nat.card (fixV A) := by
  have h1 := rkIdx_lt_of_rAV_lt hA (c := 2) (by exact_mod_cast hr)
  rw [natCard_eq_two_pow_rk hV, card_eq_two_pow_of_isPGroup hA.2.2.isPGroup,
    card_eq_two_pow hV, ← pow_mul, ← pow_add, ← rk_add_rkIdx (fixV A)]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem two_le_card_fixV (hV : ∀ v : V, v ^ 2 = 1) [Nontrivial V] {P : Subgroup (MulAut V)}
    (hP : IsPGroup 2 ↥P) : 2 ≤ Nat.card (fixV P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints V
  have hfix : Nat.card (MulAction.fixedPoints ↥P V) = Nat.card (fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hrk : 0 < rk V := by
    rcases Nat.eq_zero_or_pos (rk V) with h0 | h0
    · have h1 := natCard_eq_two_pow_rk hV
      rw [h0, pow_zero] at h1
      exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne'
    · exact h0
  have heven : Nat.card V % 2 = 0 := by
    rw [natCard_eq_two_pow_rk hV]
    obtain ⟨k, hk⟩ : ∃ k, rk V = k + 1 := ⟨rk V - 1, by omega⟩
    rw [hk, pow_succ, Nat.mul_mod_left]
  have hpos : 0 < Nat.card (fixV P) := Nat.card_pos
  have h2 : Nat.card (fixV P) % 2 = 0 := by
    have := hmod.symm
    unfold Nat.ModEq at this
    omega
  omega

end CFSG.Quasithin.SmithD37
