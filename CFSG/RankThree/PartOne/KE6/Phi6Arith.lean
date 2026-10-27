module

public import CFSG.RankThree.PartOne.KE.E6FourArith

public section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE

theorem phi6_algebra {R : Type*} [CommRing R] [NoZeroDivisors R] (Q : R)
    (hx : Q ^ 2 - Q + 1 = 0) (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) (hQ0 : Q ≠ 0) (hQ1 : Q ≠ 1) :
    orderOf Q = 6 ∧ Q + 1 ≠ 0 ∧ Q ^ 2 + Q + 1 ≠ 0 ∧ Q ^ 6 + 1 ≠ 0 := by
  have hQ3 : Q ^ 3 + 1 = 0 := by linear_combination (Q + 1) * hx
  have hQ6 : Q ^ 6 = 1 := by linear_combination (Q ^ 3 - 1) * hQ3
  refine ⟨?_, fun h0 => h3 ?_, fun h0 => ?_, fun h0 => h2 ?_⟩
  · refine (orderOf_eq_iff (by norm_num)).2 ⟨hQ6, fun m hm hm0 => ?_⟩
    interval_cases m
    · simpa using hQ1
    · intro h
      exact h3 (by linear_combination (0 - (Q + 1)) * h + (Q + 2) * hx)
    · intro h
      exact h2 (by linear_combination hQ3 - h)
    · intro h
      exact h3 (by linear_combination hx + (2 - Q) * (Q * hQ3 - h))
    · intro h
      exact hQ0 (by linear_combination Q ^ 2 * hQ3 - h - hx)
  · linear_combination hx - (Q - 2) * h0
  · have : (2 : R) * Q = 0 := by linear_combination h0 - hx
    exact (mul_eq_zero.1 this).elim h2 hQ0
  · linear_combination h0 - hQ6

theorem e6Six_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 - (q : ℤ) + 1) :
    ¬ p ∣ q ∧ orderOf (q : ZMod p) = 6 ∧ (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0 ∧
      ¬ (p : ℤ) ∣ (q : ℤ) - 1 ∧ 7 ≤ p ∧ (q : ZMod p) + 1 ≠ 0 ∧
      (q : ZMod p) ^ 2 + (q : ZMod p) + 1 ≠ 0 ∧ (q : ZMod p) ^ 6 + 1 ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 2 - (q : ℤ) + 1) p).2 h
    simpa using this
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast CTE6.natCast_ne_zero_of_lt (p := p) (c := 2) (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast CTE6.natCast_ne_zero_of_lt (p := p) (c := 3) (by norm_num) (by omega)
  have hQ0 : (q : ZMod p) ≠ 0 := fun h0 => by
    rw [h0] at hx
    simp at hx
  have hQ1 : (q : ZMod p) ≠ 1 := fun h1 => by
    rw [h1] at hx
    norm_num at hx
  obtain ⟨hord, h1, h2', h3'⟩ := phi6_algebra (q : ZMod p) hx h2 h3 hQ0 hQ1
  refine ⟨fun hd => hQ0 ((ZMod.natCast_eq_zero_iff q p).2 hd), hord, hx, fun hd => hQ1 ?_, ?_,
    h1, h2', h3'⟩
  · have h1' : (((q : ℤ) - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at h1'
    exact sub_eq_zero.1 h1'
  · have hdvd : 6 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hQ0
    omega

theorem e6Six_ordProj (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (h : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1) :
    p ^ (Nat.card (adjointGroup .E6 K)).factorization p =
      p ^ (((Nat.card K ^ 2 - Nat.card K + 1) ^ 2 * (Nat.card K ^ 2 + Nat.card K + 1) : ℕ)
        ).factorization p := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  obtain ⟨hpq, hord, hx, hq1, -, hQ2, hQ3, hQ4⟩ := e6Six_data hp hp3 h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  set n₀ : ℕ := q ^ 2 - q + 1 with hn₀def
  have hn₀ : n₀ ≠ 0 := Nat.succ_ne_zero _
  have hn₀Z : (n₀ : ℤ) = (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
    rw [hn₀def, Nat.cast_add, Nat.cast_sub hle]
    push_cast
    ring
  have hnd : ∀ y : ℤ, (y : ZMod p) ≠ 0 → ¬ (p : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 hd)
  have hc1 : ¬ (p : ℤ) ∣ (q : ℤ) - 1 := hq1
  have hc2 : ¬ (p : ℤ) ∣ (q : ℤ) + 1 := hnd _ (by push_cast; exact hQ2)
  have hc3 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 + (q : ℤ) + 1 := hnd _ (by push_cast; exact hQ3)
  have hc4 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 6 + 1 := hnd _ (by push_cast; exact hQ4)
  have hR1 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) + 1) * ((q : ℤ) ^ 2 + (q : ℤ) + 1) :=
    hpz.not_dvd_mul (hpz.not_dvd_mul hc1 hc2) hc3
  have hR2 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) + 1) * ((q : ℤ) ^ 2 + (q : ℤ) + 1) *
      ((q : ℤ) ^ 6 + 1) := hpz.not_dvd_mul hR1 hc4
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hrest : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), d ≠ 6 → d ≠ 12 → ¬ 6 ∣ d := by
    intro d hd h6 h12
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have key := ordProj_card_adjointGroup_E6_two (K := K) (p := p) (m := 6) (d₁ := 6) (d₂ := 12)
    (n₀ := n₀) (R₁ := ((q : ℤ) - 1) * ((q : ℤ) + 1) * ((q : ℤ) ^ 2 + (q : ℤ) + 1))
    (R₂ := ((q : ℤ) - 1) * ((q : ℤ) + 1) * ((q : ℤ) ^ 2 + (q : ℤ) + 1) * ((q : ℤ) ^ 6 + 1))
    hp hp3 hpq hord (by decide) (by decide) (by decide) hrest hn₀
    (by rw [hcast, hn₀Z]; ring) hR1 (by rw [hcast, hn₀Z]; ring) hR2
  have hnd3 : ¬ p ∣ q ^ 2 + q + 1 := fun hd => hc3 (by exact_mod_cast hd)
  have hordN : ordProj[p] (n₀ ^ 2 * (q ^ 2 + q + 1)) = ordProj[p] n₀ * ordProj[p] n₀ := by
    rw [sq, Nat.ordProj_mul p (mul_ne_zero hn₀ hn₀) (by positivity), Nat.ordProj_mul p hn₀ hn₀,
      CTE6.ordProj_eq_one_of_not_dvd hnd3, mul_one]
  rw [key]
  exact hordN.symm

end CFSG.RankThree.PartOne.KE6
