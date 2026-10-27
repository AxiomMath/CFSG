module

public import CFSG.RankThree.SteinbergR3EOrdinaryECrossPrimeParts
public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.RankThree.Chevalley.CubicMonomialElementaryNine

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE


theorem e8P4_ordProj {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpq : ¬ p ∣ Nat.card K) (hpf : p ∣ Nat.card K * Nat.card K + 1) :
    ordProj[p] (Nat.card (adjointGroup .E8 K)) =
      ordProj[p] ((Nat.card K * Nat.card K + 1) ^ 4) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  have : Fact p.Prime := ⟨hp⟩
  have hn₀ : q * q + 1 ≠ 0 := by positivity
  have hx : (q : ZMod p) * (q : ZMod p) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (q * q + 1) p).2 hpf
    simpa using this
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := CTE6.natCast_ne_zero_of_lt (p := p) (c := 2) (by norm_num) (by omega)
    simpa using this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := CTE6.natCast_ne_zero_of_lt (p := p) (c := 3) (by norm_num) (by omega)
    simpa using this
  have h5 : (5 : ZMod p) ≠ 0 := by
    have := CTE6.natCast_ne_zero_of_lt (p := p) (c := 5) (by norm_num) (by omega)
    simpa using this
  have hx4 : (q : ZMod p) ^ 4 = 1 := by
    linear_combination ((q : ZMod p) * (q : ZMod p) - 1) * hx
  have hord : orderOf (q : ZMod p) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨hx4, fun m hm hm0 => ?_⟩
    interval_cases m
    · intro h
      rw [pow_one] at h
      apply h2
      rw [h] at hx
      linear_combination hx
    · intro h
      apply h2
      linear_combination hx - h
    · intro h
      have h1 : (q : ZMod p) = 1 := by linear_combination hx4 - (q : ZMod p) * h
      apply h2
      rw [h1] at hx
      linear_combination hx
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have h6 : (6 : ZMod p) ≠ 0 := by
    have : (6 : ZMod p) = 2 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h3
  have h10 : (10 : ZMod p) ≠ 0 := by
    have : (10 : ZMod p) = 2 * 5 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h5
  have h12 : (12 : ZMod p) ≠ 0 := by
    have : (12 : ZMod p) = 4 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h4 h3
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hn₀Z : ((q * q + 1 : ℕ) : ℤ) = (q : ℤ) * (q : ℤ) + 1 := by push_cast; ring
  have hN : ∀ d : ℕ, 0 < d → q ^ d - 1 ≠ 0 := by
    intro d hd
    have : 1 < q ^ d := Nat.one_lt_pow hd.ne' (by omega)
    omega
  have hnd : ∀ y : ℤ, (y : ZMod p) ≠ 0 → ¬ (p : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 hd)
  have hqne : ∀ d : ℕ, ¬ 4 ∣ d → ordProj[p] (q ^ d - 1) = 1 := fun d hd =>
    CTE6.ordProj_eq_one_of_not_dvd (fun h => hd ((CTE6.dvd_pow_sub_one_iff (by omega) hord).1 h))
  have key8 : ordProj[p] (q ^ 8 - 1) = ordProj[p] (q * q + 1) :=
    CTE6.ordProj_eq_of_int_factor hn₀ (hN 8 (by norm_num))
      (R := ((q : ℤ) * (q : ℤ) - 1) * ((q : ℤ) ^ 4 + 1))
      (by rw [hcast, hn₀Z]; ring)
      (hnd _ (by
        push_cast
        intro h
        apply h4
        linear_combination ((q : ZMod p) ^ 4 - 2 * (q : ZMod p) ^ 2 + 3) * hx - h))
  have key12 : ordProj[p] (q ^ 12 - 1) = ordProj[p] (q * q + 1) :=
    CTE6.ordProj_eq_of_int_factor hn₀ (hN 12 (by norm_num))
      (R := ((q : ℤ) * (q : ℤ) - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1))
      (by rw [hcast, hn₀Z]; ring)
      (hnd _ (by
        push_cast
        intro h
        apply h6
        linear_combination ((q : ZMod p) ^ 8 - 2 * (q : ZMod p) ^ 6 + 3 * (q : ZMod p) ^ 4 -
          4 * (q : ZMod p) ^ 2 + 5) * hx - h))
  have key20 : ordProj[p] (q ^ 20 - 1) = ordProj[p] (q * q + 1) :=
    CTE6.ordProj_eq_of_int_factor hn₀ (hN 20 (by norm_num))
      (R := ((q : ℤ) * (q : ℤ) - 1) * ((q : ℤ) ^ 16 + (q : ℤ) ^ 12 + (q : ℤ) ^ 8 +
        (q : ℤ) ^ 4 + 1))
      (by rw [hcast, hn₀Z]; ring)
      (hnd _ (by
        push_cast
        intro h
        apply h10
        linear_combination ((q : ZMod p) ^ 16 - 2 * (q : ZMod p) ^ 14 + 3 * (q : ZMod p) ^ 12 -
          4 * (q : ZMod p) ^ 10 + 5 * (q : ZMod p) ^ 8 - 6 * (q : ZMod p) ^ 6 +
          7 * (q : ZMod p) ^ 4 - 8 * (q : ZMod p) ^ 2 + 9) * hx - h))
  have key24 : ordProj[p] (q ^ 24 - 1) = ordProj[p] (q * q + 1) :=
    CTE6.ordProj_eq_of_int_factor hn₀ (hN 24 (by norm_num))
      (R := ((q : ℤ) * (q : ℤ) - 1) * ((q : ℤ) ^ 20 + (q : ℤ) ^ 16 + (q : ℤ) ^ 12 +
        (q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1))
      (by rw [hcast, hn₀Z]; ring)
      (hnd _ (by
        push_cast
        intro h
        apply h12
        linear_combination ((q : ZMod p) ^ 20 - 2 * (q : ZMod p) ^ 18 + 3 * (q : ZMod p) ^ 16 -
          4 * (q : ZMod p) ^ 14 + 5 * (q : ZMod p) ^ 12 - 6 * (q : ZMod p) ^ 10 +
          7 * (q : ZMod p) ^ 8 - 8 * (q : ZMod p) ^ 6 + 9 * (q : ZMod p) ^ 4 -
          10 * (q : ZMod p) ^ 2 + 11) * hx - h))
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp
    (by omega) hpq).2.2]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [key8, key12, key20, key24, hqne 2 (by norm_num), hqne 14 (by norm_num),
    hqne 18 (by norm_num), hqne 30 (by norm_num)]
  rw [show (q * q + 1) ^ 4 = (q * q + 1) * (q * q + 1) * (q * q + 1) * (q * q + 1) by ring,
    Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero hn₀ hn₀) hn₀) hn₀,
    Nat.ordProj_mul p (mul_ne_zero hn₀ hn₀) hn₀, Nat.ordProj_mul p hn₀ hn₀]
  ring

end CFSG.RankThree.PartOne.KE8F
