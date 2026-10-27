module

public import CFSG.Quasithin.Background.B69Num
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Arith

theorem sq_sub_one_eq (x : ℕ) (hx : 1 ≤ x) : x ^ 2 - 1 = (x - 1) * (x + 1) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have : (y + 1) ^ 2 = y * (y + 1 + 1) + 1 := by ring
  rw [this]
  simp

theorem arith_psl_two_two {p n : ℕ} (hp : p.Prime) (hmod : p % 8 = 1 ∨ p % 8 = 7) (hn : 2 ≤ n)
    (h : p * (p ^ 2 - 1) = 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1))) : False := by
  set x := 2 ^ n with hx
  have hx4 : 4 ≤ x := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hxs : x ^ 2 - 1 = (x - 1) * (x + 1) := sq_sub_one_eq x (by omega)
  have hdvd : p ∣ 2 * x * ((x - 1) * (x + 1)) := by
    have h1 : p ∣ p * (p ^ 2 - 1) := Dvd.intro _ rfl
    rw [h, hxs] at h1
    simpa [mul_assoc] using h1
  have hp2 : ¬ p ∣ 2 := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    omega
  have hpx : ¬ p ∣ x := fun hd => by
    have h1 : p ∣ 2 := hp.dvd_of_dvd_pow (hx ▸ hd)
    exact hp2 h1
  have hcop : Nat.Coprime p (2 * x) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
    rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
    · exact hp2 h1
    · exact hpx h1
  have h2 : p ∣ (x - 1) * (x + 1) := hcop.dvd_of_dvd_mul_left hdvd
  have hle : p ≤ x + 1 := by
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · exact (Nat.le_of_dvd (by omega) h3).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h3
  have hx1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hint : (p : ℤ) ^ 3 - p = 2 * ((x : ℤ) ^ 3 - x) := by
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast [Nat.cast_sub hp1, Nat.cast_sub hx1] at h'
    linear_combination h'
  have hle' : (p : ℤ) ≤ x + 1 := by exact_mod_cast hle
  have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hx4' : (4 : ℤ) ≤ x := by exact_mod_cast hx4
  have hxle : x ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have hcon' : (5 : ℤ) ≤ x := by exact_mod_cast hcon
    have h1 : (p : ℤ) ^ 3 - p ≤ ((x : ℤ) + 1) ^ 3 - ((x : ℤ) + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hle') (by positivity : (0 : ℤ) ≤ (p : ℤ) ^ 2 + 1),
        mul_nonneg (sub_nonneg.mpr hle') (by positivity : (0 : ℤ) ≤ ((x : ℤ) + 1) * p),
        mul_nonneg (sub_nonneg.mpr hle') (by positivity : (0 : ℤ) ≤ ((x : ℤ) + 1) ^ 2)]
    nlinarith [h1, hint]
  have hx4e : x = 4 := le_antisymm hxle hx4
  have hp5 : p ≤ 5 := by omega
  interval_cases p
  · omega
  · exact absurd hp (by norm_num)
  · rw [hx4e] at h
    omega

theorem card_isPSL_two_odd {X : Type} [Group X] {p : ℕ} (h : IsPSL 2 p 1 X) (hp2 : p ≠ 2) :
    Nat.card X * 2 = p * (p ^ 2 - 1) := by
  have h1 := B69.card_psl_two_mul h
  have hp : p.Prime := h.1.1
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    exact Nat.gcd_eq_left (by obtain ⟨k, hk⟩ := hodd; omega)
  rw [hg, pow_one] at h1
  have hq : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have e : p ^ 3 = p * p ^ 2 := by ring
  rw [e] at h1
  rw [Nat.mul_sub, mul_one]
  omega

theorem card_isPSL_two_two {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two h

theorem two_pow_odd_mod_three {a : ℕ} : 2 ^ (2 * a + 1) % 3 = 2 := by
  induction a with
  | zero => norm_num
  | succ k ih =>
    have : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by ring
    omega

theorem not_three_dvd_card_isSz {X : Type} [Group X] {n : ℕ}
    (h : IsSz n X) : ¬ 3 ∣ Nat.card X := by
  obtain ⟨-, b, hb, F, _, _, hfb, hF, ⟨e⟩⟩ := h
  have hF' : Nat.card F = 2 ^ (2 * b + 1) := by rw [hF, hfb]
  have hc := CFSG.LieType.Ree.suzuki_order hF'
  rw [Nat.card_congr e.toEquiv, hc]
  have hq : 2 ^ (2 * b + 1) % 3 = 2 := two_pow_odd_mod_three
  set q := 2 ^ (2 * b + 1) with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ (by norm_num)
  intro hd
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  rcases (Nat.Prime.dvd_mul h3).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul h3).mp hd with hd | hd
    · have : 3 ∣ q := h3.dvd_of_dvd_pow hd
      omega
    · omega
  · omega

theorem three_dvd_card_isPSL_two_odd {X : Type} [Group X] {p : ℕ} (h : IsPSL 2 p 1 X)
    (hmod : p % 8 = 1 ∨ p % 8 = 7) : 3 ∣ Nat.card X := by
  have hp : p.Prime := h.1.1
  have hp2 : p ≠ 2 := by omega
  have h1 := card_isPSL_two_odd h hp2
  have hp3 : p ≠ 3 := by omega
  have hmod3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have : ¬ 3 ∣ p := fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd).symm
    omega
  have h3 : 3 ∣ p * (p ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ p
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    have : p ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]
      rcases hmod3 with h | h <;> rw [h]
    omega
  rw [← h1] at h3
  exact (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h3)

theorem false_of_shape_card_eq_psl_two_odd
    {X Y : Type} [Group X] [Group Y] {p : ℕ}
    (hmod : p % 8 = 1 ∨ p % 8 = 7) (hY : IsPSL 2 p 1 Y)
    (hshape : (∃ n, IsPSL 2 2 n X) ∨ (∃ n, IsSz n X) ∨ IsAlt 5 X)
    (hcard : Nat.card X = Nat.card Y) : False := by
  have hp : p.Prime := hY.1.1
  have hp2 : p ≠ 2 := by omega
  have hY2 := card_isPSL_two_odd hY hp2
  have key : ∀ n, 2 ≤ n → Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) → False := by
    intro n hn hXc
    refine arith_psl_two_two hp hmod hn ?_
    rw [← hY2, ← hcard, hXc]
    ring
  rcases hshape with ⟨n, hn⟩ | ⟨n, hn⟩ | h5
  · have hn2 : 2 ≤ n := by
      have hadm := hn.1
      have hn1 : 1 ≤ n := hadm.2.1
      by_contra hlt
      have : n = 1 := by omega
      subst this
      exact hadm.2.2.2.1 (by simp)
    exact key n hn2 (card_isPSL_two_two hn)
  · apply not_three_dvd_card_isSz hn
    rw [hcard]
    exact three_dvd_card_isPSL_two_odd hY hmod
  · have h2 := Ch1.statedClassicalModel_psl_two_four_of_alternating_five X h5
    exact key 2 le_rfl (card_isPSL_two_two h2)

end Arith

end CFSG.Quasithin.GoldS146R
