module

public import CFSG.RankThree.Chevalley.CubicMonomialElementaryNine
public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.RankThree.SteinbergR3EOrdinaryECrossPrimeParts

public section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE

theorem e6Qp_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : (p : ℤ) ∣ (q : ℤ) + 1) :
    ¬ p ∣ q ∧ orderOf (q : ZMod p) = 2 ∧ (q : ZMod p) + 1 = 0 ∧ ¬ (p : ℤ) ∣ (q : ℤ) - 1 ∧
      5 ≤ p ∧ ¬ (p : ℤ) ∣ 3 ∧ ¬ (p : ℤ) ∣ 4 ∧ ¬ (p : ℤ) ∣ 6 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) + 1) p).2 h
    simpa using this
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have : p = 4 := by omega
    exact absurd (this ▸ hp) (by norm_num)
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast CTE6.natCast_ne_zero_of_lt (p := p) (c := 2) (by norm_num) (by omega)
  have hQ1 : (q : ZMod p) ≠ 1 := fun h1 => by
    rw [h1] at hx
    apply h2
    linear_combination hx
  have hQ0 : (q : ZMod p) ≠ 0 := fun h0 => by
    rw [h0] at hx
    simp at hx
  have hQ2 : (q : ZMod p) ^ 2 = 1 := by linear_combination ((q : ZMod p) - 1) * hx
  have hord : orderOf (q : ZMod p) = 2 := by
    refine (orderOf_eq_iff (by norm_num)).2 ⟨hQ2, fun m hm hm0 => ?_⟩
    interval_cases m
    simpa using hQ1
  refine ⟨fun hd => hQ0 ((ZMod.natCast_eq_zero_iff q p).2 hd), hord, hx, fun hd => hQ1 ?_, hp5,
    ?_, ?_, ?_⟩
  · have h1' : (((q : ℤ) - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at h1'
    exact sub_eq_zero.1 h1'
  · exact_mod_cast CTE6.not_dvd_natCast_of_lt (p := p) (c := 3) (by norm_num) (by omega)
  · exact_mod_cast CTE6.not_dvd_natCast_of_lt (p := p) (c := 4) (by norm_num) (by omega)
  · intro h6
    have h6' : p ∣ 6 := by exact_mod_cast h6
    have hle := Nat.le_of_dvd (by norm_num) h6'
    have : p = 5 ∨ p = 6 := by omega
    rcases this with rfl | rfl
    · omega
    · exact absurd hp (by norm_num)

theorem e6Qp_ordProj (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (h : (p : ℤ) ∣ (Nat.card K : ℤ) + 1) :
    p ^ (Nat.card (adjointGroup .E6 K)).factorization p =
      p ^ (((Nat.card K + 1) ^ 4 * (Nat.card K - 1) ^ 2 : ℕ)).factorization p := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  obtain ⟨hpq, hord, hx, hq1, hp5, h3, h4, h6⟩ := e6Qp_data hp hp3 h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hq1' : 1 ≤ q := by omega
  have hN : ∀ d : ℕ, 0 < d → q ^ d - 1 ≠ 0 := by
    intro d hd
    have : 1 < q ^ d := Nat.one_lt_pow hd.ne' (by omega)
    omega
  have hR1 : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) := by
    intro hd
    have hx' : (((q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at hx'
    have hQ2 : (q : ZMod p) ^ 2 = 1 := by linear_combination ((q : ZMod p) - 1) * hx
    have hQ4 : (q : ZMod p) ^ 4 = 1 := by linear_combination ((q : ZMod p) ^ 2 + 1) * hQ2
    apply h3
    have : ((3 : ℤ) : ZMod p) = 0 := by
      push_cast
      linear_combination hx' - hQ4 - hQ2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).1 this
  have hR2 : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) := by
    intro hd
    have hx' : (((q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at hx'
    have hQ2 : (q : ZMod p) ^ 2 = 1 := by linear_combination ((q : ZMod p) - 1) * hx
    have hQ4 : (q : ZMod p) ^ 4 = 1 := by linear_combination ((q : ZMod p) ^ 2 + 1) * hQ2
    have hQ6 : (q : ZMod p) ^ 6 = 1 := by linear_combination ((q : ZMod p) ^ 4 + (q : ZMod p) ^ 2 + 1) * hQ2
    apply h4
    have : ((4 : ℤ) : ZMod p) = 0 := by
      push_cast
      linear_combination hx' - hQ6 - hQ4 - hQ2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd 4 p).1 this
  have hR3 : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 10 + (q : ℤ) ^ 8 + (q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) := by
    intro hd
    have hx' : (((q : ℤ) ^ 10 + (q : ℤ) ^ 8 + (q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1 : ℤ) :
        ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at hx'
    have hQ2 : (q : ZMod p) ^ 2 = 1 := by linear_combination ((q : ZMod p) - 1) * hx
    have hQ4 : (q : ZMod p) ^ 4 = 1 := by linear_combination ((q : ZMod p) ^ 2 + 1) * hQ2
    have hQ6 : (q : ZMod p) ^ 6 = 1 := by linear_combination ((q : ZMod p) ^ 4 + (q : ZMod p) ^ 2 + 1) * hQ2
    have hQ8 : (q : ZMod p) ^ 8 = 1 := by
      linear_combination ((q : ZMod p) ^ 6 + (q : ZMod p) ^ 4 + (q : ZMod p) ^ 2 + 1) * hQ2
    have hQ10 : (q : ZMod p) ^ 10 = 1 := by
      linear_combination ((q : ZMod p) ^ 8 + (q : ZMod p) ^ 6 + (q : ZMod p) ^ 4 +
        (q : ZMod p) ^ 2 + 1) * hQ2
    apply h6
    have : ((6 : ℤ) : ZMod p) = 0 := by
      push_cast
      linear_combination hx' - hQ10 - hQ8 - hQ6 - hQ4 - hQ2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd 6 p).1 this
  have hn₀ : q ^ 2 - 1 ≠ 0 := hN 2 (by norm_num)
  have hn₀Z : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := hcast 2
  have h6 := CTE6.ordProj_eq_of_int_factor hn₀ (hN 6 (by norm_num))
    (R := (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) (by rw [hcast, hn₀Z]; ring) hR1
  have h8 := CTE6.ordProj_eq_of_int_factor hn₀ (hN 8 (by norm_num))
    (R := (q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) (by rw [hcast, hn₀Z]; ring) hR2
  have h12 := CTE6.ordProj_eq_of_int_factor hn₀ (hN 12 (by norm_num))
    (R := (q : ℤ) ^ 10 + (q : ℤ) ^ 8 + (q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1)
    (by rw [hcast, hn₀Z]; ring) hR3
  have h5 : ordProj[p] (q ^ 5 - 1) = 1 :=
    CTE6.ordProj_eq_one_of_not_dvd fun hd => by
      have := (CTE6.dvd_pow_sub_one_iff hq1' hord).1 hd
      omega
  have h9 : ordProj[p] (q ^ 9 - 1) = 1 :=
    CTE6.ordProj_eq_one_of_not_dvd fun hd => by
      have := (CTE6.dvd_pow_sub_one_iff hq1' hord).1 hd
      omega
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp hp3 hpq).1]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [h5, h9, h6, h8, h12]
  have hq1n : q - 1 ≠ 0 := by omega
  have hq1p : ordProj[p] (q - 1) = 1 :=
    CTE6.ordProj_eq_one_of_not_dvd fun hd => hq1 (by
      have := Int.natCast_dvd_natCast.2 hd
      rwa [Nat.cast_sub hq1', Nat.cast_one] at this)
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have key : ∀ n : ℕ, n ^ 2 - 1 = (n - 1) * (n + 1) := by
      intro n
      cases n with
      | zero => simp
      | succ k =>
        simp only [Nat.add_sub_cancel]
        exact Nat.sub_eq_of_eq_add (by ring)
    exact key q
  have hqp1 : q + 1 ≠ 0 := Nat.succ_ne_zero _
  have hfa : ordProj[p] (q ^ 2 - 1) = ordProj[p] (q + 1) := by
    rw [hfac, Nat.ordProj_mul p hq1n hqp1, hq1p, one_mul]
  have hT : ordProj[p] ((q + 1) ^ 4 * (q - 1) ^ 2) = ordProj[p] (q + 1) ^ 4 := by
    have hpow : ∀ (a n : ℕ), a ≠ 0 → ordProj[p] (a ^ n) = ordProj[p] a ^ n := fun a n ha => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Nat.ordProj_mul p (pow_ne_zero n ha) ha, ih, pow_succ]
    rw [Nat.ordProj_mul p (pow_ne_zero 4 hqp1) (pow_ne_zero 2 hq1n), hpow _ _ hqp1,
      hpow _ _ hq1n, hq1p, one_pow, mul_one]
  rw [hT, hfa]
  ring

end CFSG.RankThree.PartOne.KE6
