module

public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE.CTE6

theorem f4Three_odd (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (q : ℕ) :
    Odd (((q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs) := by
  rw [Int.natAbs_odd]
  have hδo : Odd δ := by rcases hδ with rfl | rfl <;> decide
  rcases Int.even_or_odd (q : ℤ) with he | ho
  · obtain ⟨k, hk⟩ := he
    exact ⟨2 * k ^ 2 + δ * k, by rw [hk]; ring⟩
  · have h1 : Odd ((q : ℤ) ^ 2) := ho.pow
    have h2 : Odd (δ * (q : ℤ)) := hδo.mul ho
    exact (h1.add_odd h2).add_one

theorem f4Three_hΦ_one {p : ℕ} (q : ℕ)
    (h : (q : ZMod p) ^ 2 + (q : ZMod p) + 1 = 0) :
    (((1 : ℤ) : ZMod p) * (q : ZMod p)) ^ 2 + ((1 : ℤ) : ZMod p) * (q : ZMod p) + 1 = 0 := by
  simpa using h

theorem f4Three_hΦ_neg {p : ℕ} (q : ℕ)
    (h : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    (((-1 : ℤ) : ZMod p) * (q : ZMod p)) ^ 2 + ((-1 : ℤ) : ZMod p) * (q : ZMod p) + 1 = 0 := by
  have : (-(q : ZMod p)) ^ 2 + -(q : ZMod p) + 1 = 0 := by
    rw [← sub_eq_add_neg, neg_sq]
    exact h
  simpa using this

theorem f4Three_zmod_facts {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (d y : ZMod p) (hd : d * d = 1)
    (hΦ : (d * y) ^ 2 + (d * y) + 1 = 0) :
    y ≠ 0 ∧ y - d ≠ 0 ∧ y ^ 3 + d ≠ 0 ∧ y ^ 6 + 1 ≠ 0 ∧ y ^ 2 - 1 ≠ 0 ∧ y ^ 8 - 1 ≠ 0 := by
  have hdom : IsDomain (ZMod p) := by
    have : Fact p.Prime := ⟨hp⟩
    infer_instance
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) hp3
  have h2' : (2 : ZMod p) ≠ 0 := by simpa using h2
  have h3' : (3 : ZMod p) ≠ 0 := by simpa using h3
  have hd3 : d ^ 3 = d := by
    calc d ^ 3 = (d * d) * d := by ring
      _ = d := by rw [hd]; ring
  have hdu : d ≠ 0 := fun h0 => by
    rw [h0] at hd
    simp at hd
  have hx3 : (d * y) ^ 3 = 1 := by
    linear_combination (d * y - 1) * hΦ
  have hy3 : y ^ 3 = d := by
    have h : d * y ^ 3 = 1 := by
      calc d * y ^ 3 = (d * y) ^ 3 := by rw [mul_pow, hd3]
        _ = 1 := hx3
    calc y ^ 3 = (d * d) * y ^ 3 := by rw [hd, one_mul]
      _ = d * (d * y ^ 3) := by ring
      _ = d := by rw [h, mul_one]
  have hy6 : y ^ 6 = 1 := by
    calc y ^ 6 = (y ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hy3]; linear_combination hd
  have hy0 : y ≠ 0 := fun h0 => by
    rw [h0] at hΦ
    simp at hΦ
  have hy1 : y - 1 ≠ 0 := fun h => by
    have hy : y = 1 := sub_eq_zero.1 h
    rw [hy] at hΦ
    apply h3'
    linear_combination (d - 1) * hd - (d - 2) * hΦ
  have hym1 : y + 1 ≠ 0 := fun h => by
    have hy : y = -1 := eq_neg_of_add_eq_zero_left h
    rw [hy] at hΦ
    apply h3'
    linear_combination (d + 2) * hΦ - (d + 1) * hd
  refine ⟨hy0, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hyd : y = d := sub_eq_zero.1 h
    rw [hyd, hd] at hΦ
    apply h3'
    linear_combination hΦ
  · intro h
    rw [hy3] at h
    apply h2'
    have : d * (2 : ZMod p) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left hdu
  · intro h
    rw [hy6] at h
    apply h2'
    linear_combination h
  · intro h
    have : (y - 1) * (y + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hy1 h'
    · exact hym1 h'
  · intro h
    have h8 : y ^ 8 = y ^ 2 := by
      calc y ^ 8 = y ^ 6 * y ^ 2 := by ring
        _ = y ^ 2 := by rw [hy6, one_mul]
    rw [h8] at h
    have : (y - 1) * (y + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hy1 h'
    · exact hym1 h'

theorem f4ThreeF_pos (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {q : ℕ} (hq : 2 ≤ q) :
    0 < (q : ℤ) ^ 2 + δ * (q : ℤ) + 1 := by
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  rcases hδ with rfl | rfl <;> nlinarith

theorem f4Three_ordProj
    (K : Type) [Field K] [Finite K] (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p)
    (hΦ : (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      ((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p) + 1 = 0) :
    ordProj[p] (Nat.card (adjointGroup .F4 K)) =
      ordProj[p] ((((Nat.card K : ℤ) ^ 2 + δ * (Nat.card K : ℤ) + 1).natAbs) ^ 2) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  set q : ℕ := Nat.card K with hqdef
  set F : ℤ := (q : ℤ) ^ 2 + δ * (q : ℤ) + 1 with hF
  have hFpos : 0 < F := f4ThreeF_pos δ hδ hq2
  set n₀ : ℕ := F.natAbs with hn₀def
  have hn₀ : (n₀ : ℤ) = F := Int.natAbs_of_nonneg hFpos.le
  have hn₀ne : n₀ ≠ 0 := Int.natAbs_ne_zero.2 hFpos.ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hy0, hf1, hf2, hf3, hf4, hf5⟩ := f4Three_zmod_facts hp hp3 ((δ : ℤ) : ZMod p)
    ((q : ℕ) : ZMod p) (by rw [← Int.cast_mul, hδ2]; simp) hΦ
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
    apply hf4
    have := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)] at this
    simpa using this
  have hp8 : ¬ p ∣ q ^ 8 - 1 := fun h => by
    apply hf5
    have := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)] at this
    simpa using this
  have hR1 : ¬ (p : ℤ) ∣ ((q : ℤ) - δ) * ((q : ℤ) ^ 3 + δ) := by
    refine hpz.not_dvd_mul (hnd _ ?_) (hnd _ ?_)
    · push_cast
      exact hf1
    · push_cast
      exact hf2
  have hR2 : ¬ (p : ℤ) ∣ ((q : ℤ) - δ) * ((q : ℤ) ^ 3 + δ) * ((q : ℤ) ^ 6 + 1) := by
    refine hpz.not_dvd_mul (hpz.not_dvd_mul (hnd _ ?_) (hnd _ ?_)) (hnd _ ?_)
    · push_cast
      exact hf1
    · push_cast
      exact hf2
    · push_cast
      exact hf3
  have e6 : ordProj[p] (q ^ 6 - 1) = ordProj[p] n₀ :=
    ordProj_eq_of_int_factor hn₀ne (hN 6 (by norm_num))
      (R := ((q : ℤ) - δ) * ((q : ℤ) ^ 3 + δ))
      (by rw [hcast, hn₀, hF]; rcases hδ with rfl | rfl <;> ring) hR1
  have e12 : ordProj[p] (q ^ 12 - 1) = ordProj[p] n₀ :=
    ordProj_eq_of_int_factor hn₀ne (hN 12 (by norm_num))
      (R := ((q : ℤ) - δ) * ((q : ℤ) ^ 3 + δ) * ((q : ℤ) ^ 6 + 1))
      (by rw [hcast, hn₀, hF]; rcases hδ with rfl | rfl <;> ring) hR2
  have h24 : q ^ 24 ≠ 0 := by positivity
  have h12 := hN 12 (by norm_num)
  have h8 := hN 8 (by norm_num)
  have h6 := hN 6 (by norm_num)
  have h2 := hN 2 (by norm_num)
  rw [hcard, Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero (mul_ne_zero h24 h12) h8) h6) h2,
    Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero h24 h12) h8) h6,
    Nat.ordProj_mul p (mul_ne_zero h24 h12) h8, Nat.ordProj_mul p h24 h12,
    ordProj_eq_one_of_not_dvd hpq, ordProj_eq_one_of_not_dvd hp2, ordProj_eq_one_of_not_dvd hp8,
    e6, e12, sq, Nat.ordProj_mul p hn₀ne hn₀ne]
  ring

end CFSG.RankThree.PartOne.KF4
