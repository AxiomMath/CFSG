module

public import CFSG.RankThree.Chevalley.CubicMonomialElementaryNine
public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.RankThree.SteinbergR3EOrdinaryECrossPrimeParts

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE


theorem e8P4_ordProj_five {K : Type} [Field K] [Finite K]
    (hpf : 5 ∣ Nat.card K * Nat.card K + 1) :
    ordProj[5] (Nat.card (adjointGroup .E8 K)) =
      5 * ordProj[5] ((Nat.card K * Nat.card K + 1) ^ 4) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  have hp : Nat.Prime 5 := by norm_num
  have hpq : ¬ 5 ∣ q := fun h => by
    have h1 : 5 ∣ q * q := Dvd.dvd.mul_right h _
    have := (Nat.dvd_add_right h1).1 hpf
    exact absurd (Nat.dvd_one.1 this) (by norm_num)
  have hn₀ : q * q + 1 ≠ 0 := by positivity
  have hx : (q : ZMod 5) * (q : ZMod 5) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (q * q + 1) 5).2 hpf
    simpa using this
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have h4 : (4 : ZMod 5) ≠ 0 := by decide
  have h6 : (6 : ZMod 5) ≠ 0 := by decide
  have h12 : (12 : ZMod 5) ≠ 0 := by decide
  have hx4 : (q : ZMod 5) ^ 4 = 1 := by
    linear_combination ((q : ZMod 5) * (q : ZMod 5) - 1) * hx
  have hord : orderOf (q : ZMod 5) = 4 := by
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
      have h1 : (q : ZMod 5) = 1 := by linear_combination hx4 - (q : ZMod 5) * h
      apply h2
      rw [h1] at hx
      linear_combination hx
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hn₀Z : ((q * q + 1 : ℕ) : ℤ) = (q : ℤ) * (q : ℤ) + 1 := by push_cast; ring
  have hN : ∀ d : ℕ, 0 < d → q ^ d - 1 ≠ 0 := by
    intro d hd
    have : 1 < q ^ d := Nat.one_lt_pow hd.ne' (by omega)
    omega
  have hnd : ∀ y : ℤ, (y : ZMod 5) ≠ 0 → ¬ ((5 : ℕ) : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y 5).2 hd)
  have hqne : ∀ d : ℕ, ¬ 4 ∣ d → ordProj[5] (q ^ d - 1) = 1 := fun d hd =>
    CTE6.ordProj_eq_one_of_not_dvd (fun h => hd ((CTE6.dvd_pow_sub_one_iff (by omega) hord).1 h))
  have key8 : ordProj[5] (q ^ 8 - 1) = ordProj[5] (q * q + 1) :=
    CTE6.ordProj_eq_of_int_factor hn₀ (hN 8 (by norm_num))
      (R := ((q : ℤ) * (q : ℤ) - 1) * ((q : ℤ) ^ 4 + 1))
      (by rw [hcast, hn₀Z]; ring)
      (hnd _ (by
        push_cast
        intro h
        apply h4
        linear_combination ((q : ZMod 5) ^ 4 - 2 * (q : ZMod 5) ^ 2 + 3) * hx - h))
  have key12 : ordProj[5] (q ^ 12 - 1) = ordProj[5] (q * q + 1) :=
    CTE6.ordProj_eq_of_int_factor hn₀ (hN 12 (by norm_num))
      (R := ((q : ℤ) * (q : ℤ) - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1))
      (by rw [hcast, hn₀Z]; ring)
      (hnd _ (by
        push_cast
        intro h
        apply h6
        linear_combination ((q : ZMod 5) ^ 8 - 2 * (q : ZMod 5) ^ 6 + 3 * (q : ZMod 5) ^ 4 -
          4 * (q : ZMod 5) ^ 2 + 5) * hx - h))
  have key24 : ordProj[5] (q ^ 24 - 1) = ordProj[5] (q * q + 1) :=
    CTE6.ordProj_eq_of_int_factor hn₀ (hN 24 (by norm_num))
      (R := ((q : ℤ) * (q : ℤ) - 1) * ((q : ℤ) ^ 20 + (q : ℤ) ^ 16 + (q : ℤ) ^ 12 +
        (q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1))
      (by rw [hcast, hn₀Z]; ring)
      (hnd _ (by
        push_cast
        intro h
        apply h12
        linear_combination ((q : ZMod 5) ^ 20 - 2 * (q : ZMod 5) ^ 18 + 3 * (q : ZMod 5) ^ 16 -
          4 * (q : ZMod 5) ^ 14 + 5 * (q : ZMod 5) ^ 12 - 6 * (q : ZMod 5) ^ 10 +
          7 * (q : ZMod 5) ^ 8 - 8 * (q : ZMod 5) ^ 6 + 9 * (q : ZMod 5) ^ 4 -
          10 * (q : ZMod 5) ^ 2 + 11) * hx - h))
  have key20 : ordProj[5] (q ^ 20 - 1) = 5 * ordProj[5] (q * q + 1) := by
    obtain ⟨k, hk⟩ := hpf
    set m : ℤ := 5 * (k : ℤ) ^ 2 - 2 * k with hm
    have hq4 : (q : ℤ) ^ 4 = 1 + 5 * m := by
      have h1 : (q : ℤ) * q + 1 = 5 * k := by exact_mod_cast hk
      have h2' : (q : ℤ) * q = 5 * k - 1 := by linarith
      calc (q : ℤ) ^ 4 = ((q : ℤ) * q) ^ 2 := by ring
        _ = 1 + 5 * m := by rw [h2', hm]; ring
    set R₁ : ℤ := 1 + 10 * m + 50 * m ^ 2 + 125 * m ^ 3 + 125 * m ^ 4 with hR₁
    set R₂ : ℤ := ((q : ℤ) * q - 1) * R₁ with hR₂
    have hfac : ((q ^ 20 - 1 : ℕ) : ℤ) = ((q * q + 1 : ℕ) : ℤ) * (5 * R₂) := by
      rw [hcast, hn₀Z, hR₂]
      have e1 : (q : ℤ) ^ 20 = ((q : ℤ) ^ 4) ^ 5 := by ring
      have e2 : ((q : ℤ) ^ 4) ^ 5 - 1 = ((q : ℤ) ^ 4 - 1) * (((q : ℤ) ^ 4) ^ 4 +
          ((q : ℤ) ^ 4) ^ 3 + ((q : ℤ) ^ 4) ^ 2 + (q : ℤ) ^ 4 + 1) := by ring
      have e3 : ((q : ℤ) ^ 4) ^ 4 + ((q : ℤ) ^ 4) ^ 3 + ((q : ℤ) ^ 4) ^ 2 + (q : ℤ) ^ 4 + 1 =
          5 * R₁ := by rw [hq4, hR₁]; ring
      have e4 : (q : ℤ) ^ 4 - 1 = ((q : ℤ) * q - 1) * ((q : ℤ) * q + 1) := by ring
      rw [e1, show (q : ℤ) ^ 4 = (q : ℤ) ^ 4 from rfl]
      calc ((q : ℤ) ^ 4) ^ 5 - 1 = ((q : ℤ) ^ 4 - 1) * (5 * R₁) := by rw [e2, e3]
        _ = ((q : ℤ) * q + 1) * (5 * (((q : ℤ) * q - 1) * R₁)) := by rw [e4]; ring
    have hR₂nd : ¬ ((5 : ℕ) : ℤ) ∣ R₂ := by
      apply hnd
      rw [hR₂, hR₁]
      push_cast
      have h10 : (10 : ZMod 5) = 0 := by decide
      have h50 : (50 : ZMod 5) = 0 := by decide
      have h125 : (125 : ZMod 5) = 0 := by decide
      rw [h10, h50, h125]
      intro h
      apply h2
      linear_combination hx - h
    have hR20 : R₂ ≠ 0 := fun h0 => hR₂nd (by rw [h0]; exact dvd_zero _)
    have hN20 : q ^ 20 - 1 ≠ 0 := hN 20 (by norm_num)
    have hNn : q ^ 20 - 1 = (q * q + 1) * (5 * R₂).natAbs := by
      have h1 := congrArg Int.natAbs hfac
      rw [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_natCast] at h1
      exact h1
    have hR2n : R₂.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hR20
    have h5R2 : ¬ 5 ∣ R₂.natAbs := fun h => hR₂nd (Int.natCast_dvd.2 h)
    rw [hNn, Int.natAbs_mul, Nat.ordProj_mul 5 hn₀ (mul_ne_zero (by norm_num) hR2n),
      Nat.ordProj_mul 5 (by norm_num) hR2n, CTE6.ordProj_eq_one_of_not_dvd h5R2, mul_one,
      mul_comm]
    congr 1
    simp [Nat.factorization]
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp
    (by norm_num) hpq).2.2]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [key8, key12, key20, key24, hqne 2 (by norm_num), hqne 14 (by norm_num),
    hqne 18 (by norm_num), hqne 30 (by norm_num)]
  rw [show (q * q + 1) ^ 4 = (q * q + 1) * (q * q + 1) * (q * q + 1) * (q * q + 1) by ring,
    Nat.ordProj_mul 5 (mul_ne_zero (mul_ne_zero hn₀ hn₀) hn₀) hn₀,
    Nat.ordProj_mul 5 (mul_ne_zero hn₀ hn₀) hn₀, Nat.ordProj_mul 5 hn₀ hn₀]
  ring

end CFSG.RankThree.PartOne.KE8F
