module

public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE.CTE6

theorem f4Four_zmod_facts {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (y : ZMod p) (hΦ : y ^ 2 + 1 = 0) :
    y ≠ 0 ∧ y ^ 2 - 1 ≠ 0 ∧ y ^ 4 + 1 ≠ 0 ∧ y ^ 6 - 1 ≠ 0 ∧ y ^ 8 + y ^ 4 + 1 ≠ 0 := by
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) hp3
  have h2' : (2 : ZMod p) ≠ 0 := by simpa using h2
  have h3' : (3 : ZMod p) ≠ 0 := by simpa using h3
  have hy2 : y ^ 2 = -1 := eq_neg_of_add_eq_zero_left hΦ
  have hy4 : y ^ 4 = 1 := by
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hy2]; ring
  have hy6 : y ^ 6 = -1 := by
    calc y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = -1 := by rw [hy2]; ring
  have hy8 : y ^ 8 = 1 := by
    calc y ^ 8 = (y ^ 4) ^ 2 := by ring
      _ = 1 := by rw [hy4]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [h0] at hΦ
    have : Fact p.Prime := ⟨hp⟩
    simp at hΦ
  · intro h
    rw [hy2] at h
    apply h2'
    linear_combination -h
  · intro h
    rw [hy4] at h
    apply h2'
    linear_combination h
  · intro h
    rw [hy6] at h
    apply h2'
    linear_combination -h
  · intro h
    rw [hy8, hy4] at h
    apply h3'
    linear_combination h

theorem f4Four_ordProj
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0) :
    ordProj[p] (Nat.card (adjointGroup .F4 K)) = ordProj[p] ((Nat.card K ^ 2 + 1) ^ 2) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  set n₀ : ℕ := q ^ 2 + 1 with hn₀def
  have hn₀ne : n₀ ≠ 0 := by positivity
  have hn₀ : (n₀ : ℤ) = (q : ℤ) ^ 2 + 1 := by
    rw [hn₀def]
    push_cast
    ring
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hy0, hf2, hf4, hf6, hf8⟩ := f4Four_zmod_facts hp hp3 ((q : ℕ) : ZMod p) hΦ
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnd : ∀ y : ℤ, (y : ZMod p) ≠ 0 → ¬ (p : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 hd)
  have hq1 : 1 ≤ q := by omega
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow, Nat.cast_one]
  have hcard : Nat.card (adjointGroup .F4 K) =
      q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    rfl
  have hN : ∀ d : ℕ, 0 < d → q ^ d - 1 ≠ 0 := by
    intro d hd
    have : 1 < q ^ d := Nat.one_lt_pow hd.ne' (by omega)
    omega
  have hpq : ¬ p ∣ q ^ 24 := fun h => by
    have h1 : p ∣ q := hp.dvd_of_dvd_pow h
    exact hy0 ((ZMod.natCast_eq_zero_iff q p).2 h1)
  have hp2 : ¬ p ∣ q ^ 2 - 1 := fun h => by
    apply hf2
    have := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)] at this
    simpa using this
  have hp6 : ¬ p ∣ q ^ 6 - 1 := fun h => by
    apply hf6
    have := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)] at this
    simpa using this
  have hR8 : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 + 1) := by
    refine hpz.not_dvd_mul (hnd _ ?_) (hnd _ ?_)
    · push_cast
      exact hf2
    · push_cast
      exact hf4
  have hR12 : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) := by
    refine hpz.not_dvd_mul (hnd _ ?_) (hnd _ ?_)
    · push_cast
      exact hf2
    · push_cast
      exact hf8
  have e8 : ordProj[p] (q ^ 8 - 1) = ordProj[p] n₀ :=
    ordProj_eq_of_int_factor hn₀ne (hN 8 (by norm_num))
      (R := ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 + 1))
      (by rw [hcast, hn₀]; ring) hR8
  have e12 : ordProj[p] (q ^ 12 - 1) = ordProj[p] n₀ :=
    ordProj_eq_of_int_factor hn₀ne (hN 12 (by norm_num))
      (R := ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1))
      (by rw [hcast, hn₀]; ring) hR12
  have h24 : q ^ 24 ≠ 0 := by positivity
  have h12 := hN 12 (by norm_num)
  have h8 := hN 8 (by norm_num)
  have h6 := hN 6 (by norm_num)
  have h2 := hN 2 (by norm_num)
  rw [hcard, Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero (mul_ne_zero h24 h12) h8) h6) h2,
    Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero h24 h12) h8) h6,
    Nat.ordProj_mul p (mul_ne_zero h24 h12) h8, Nat.ordProj_mul p h24 h12,
    ordProj_eq_one_of_not_dvd hpq, ordProj_eq_one_of_not_dvd hp2, ordProj_eq_one_of_not_dvd hp6,
    e8, e12, sq, Nat.ordProj_mul p hn₀ne hn₀ne]
  ring

end CFSG.RankThree.PartOne.KF4
