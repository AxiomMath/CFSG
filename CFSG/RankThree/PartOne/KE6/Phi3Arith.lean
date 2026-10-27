module

public import CFSG.RankThree.Chevalley.CubicMonomialElementaryNine
public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.RankThree.SteinbergR3EOrdinaryECrossPrimeParts

public section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE

theorem phi3_algebra {R : Type*} [CommRing R] [NoZeroDivisors R] (Q : R)
    (hx : Q ^ 2 + Q + 1 = 0) (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) (hQ1 : Q ≠ 1) :
    orderOf Q = 3 ∧ Q + 1 ≠ 0 ∧ Q ^ 3 + 1 ≠ 0 ∧ Q ^ 6 + Q ^ 3 + 1 ≠ 0 ∧ Q ^ 6 + 1 ≠ 0 := by
  have hQ3 : Q ^ 3 = 1 := by linear_combination (Q - 1) * hx
  have hQ6 : Q ^ 6 = 1 := by linear_combination (Q ^ 3 + 1) * hQ3
  refine ⟨?_, fun h0 => h2 ?_, fun h0 => h2 ?_, fun h0 => h3 ?_, fun h0 => h2 ?_⟩
  · refine (orderOf_eq_iff (by norm_num)).2 ⟨hQ3, fun m hm hm0 => ?_⟩
    interval_cases m
    · simpa using hQ1
    · intro h
      exact h3 (by linear_combination (Q - 1) * h - (Q - 2) * hx)
  · have h1 : (1 : R) = 0 := by linear_combination hx - Q * h0
    linear_combination 2 * h1
  · linear_combination h0 - hQ3
  · linear_combination h0 - hQ6 - hQ3
  · linear_combination h0 - hQ6

theorem e6Three_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 + (q : ℤ) + 1) :
    ¬ p ∣ q ∧ orderOf (q : ZMod p) = 3 ∧ (q : ZMod p) ^ 2 + (q : ZMod p) + 1 = 0 ∧
      ¬ (p : ℤ) ∣ (q : ℤ) - 1 ∧ 7 ≤ p ∧ (q : ZMod p) + 1 ≠ 0 ∧ (q : ZMod p) ^ 3 + 1 ≠ 0 ∧
      (q : ZMod p) ^ 6 + (q : ZMod p) ^ 3 + 1 ≠ 0 ∧ (q : ZMod p) ^ 6 + 1 ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) ^ 2 + (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 2 + (q : ℤ) + 1) p).2 h
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
    apply h3
    linear_combination hx
  obtain ⟨hord, h1, h2', h3', h4'⟩ := phi3_algebra (q : ZMod p) hx h2 h3 hQ1
  refine ⟨fun hd => hQ0 ((ZMod.natCast_eq_zero_iff q p).2 hd), hord, hx, fun hd => hQ1 ?_, ?_,
    h1, h2', h3', h4'⟩
  · have h1' : (((q : ℤ) - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at h1'
    exact sub_eq_zero.1 h1'
  · have hdvd : 3 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hQ0
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · obtain ⟨k, hk⟩ := h
      omega

theorem prod_map_ordProj_eq_three {p q m : ℕ} (hq : 1 ≤ q) (hord : orderOf (q : ZMod p) = m)
    {D : List ℕ} (hD : D.Nodup) {d₁ d₂ d₃ : ℕ} (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hd₃ : d₃ ∈ D)
    (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃)
    (hrest : ∀ d ∈ D, d ≠ d₁ → d ≠ d₂ → d ≠ d₃ → ¬ m ∣ d) :
    (D.map fun d => ordProj[p] (q ^ d - 1)).prod =
      ordProj[p] (q ^ d₁ - 1) * ordProj[p] (q ^ d₂ - 1) * ordProj[p] (q ^ d₃ - 1) := by
  rw [← List.prod_map_erase _ hd₁]
  have hd₂' : d₂ ∈ D.erase d₁ := (hD.mem_erase_iff).2 ⟨h12.symm, hd₂⟩
  rw [← List.prod_map_erase _ hd₂']
  have hd₃' : d₃ ∈ (D.erase d₁).erase d₂ := ((hD.erase d₁).mem_erase_iff).2 ⟨h23.symm,
    (hD.mem_erase_iff).2 ⟨h13.symm, hd₃⟩⟩
  rw [← List.prod_map_erase _ hd₃']
  have h1 : ((((D.erase d₁).erase d₂).erase d₃).map fun d => ordProj[p] (q ^ d - 1)).prod = 1 := by
    refine List.prod_eq_one fun y hy => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
    have hDe : (D.erase d₁).Nodup := hD.erase d₁
    have hDe2 : ((D.erase d₁).erase d₂).Nodup := hDe.erase d₂
    rw [hDe2.mem_erase_iff, hDe.mem_erase_iff, hD.mem_erase_iff] at hd
    exact CTE6.ordProj_eq_one_of_not_dvd (fun h => hrest d hd.2.2.2 hd.2.2.1 hd.2.1 hd.1
      ((CTE6.dvd_pow_sub_one_iff hq hord).1 h))
  rw [h1, mul_one]
  ring

theorem ordProj_card_adjointGroup_E6_three {K : Type} [Field K] [Finite K]
    {p m d₁ d₂ d₃ n₀ : ℕ} {R₁ R₂ R₃ : ℤ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₁ : d₁ ∈ ([2, 5, 6, 8, 9, 12] : List ℕ))
    (hd₂ : d₂ ∈ ([2, 5, 6, 8, 9, 12] : List ℕ)) (hd₃ : d₃ ∈ ([2, 5, 6, 8, 9, 12] : List ℕ))
    (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃)
    (hrest : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), d ≠ d₁ → d ≠ d₂ → d ≠ d₃ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac₁ : ((Nat.card K ^ d₁ - 1 : ℕ) : ℤ) = n₀ * R₁) (hR₁ : ¬ (p : ℤ) ∣ R₁)
    (hfac₂ : ((Nat.card K ^ d₂ - 1 : ℕ) : ℤ) = n₀ * R₂) (hR₂ : ¬ (p : ℤ) ∣ R₂)
    (hfac₃ : ((Nat.card K ^ d₃ - 1 : ℕ) : ℤ) = n₀ * R₃) (hR₃ : ¬ (p : ℤ) ∣ R₃) :
    ordProj[p] (Nat.card (adjointGroup .E6 K)) =
      ordProj[p] n₀ * ordProj[p] n₀ * ordProj[p] n₀ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hdpos : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), 0 < d := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have hN : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), Nat.card K ^ d - 1 ≠ 0 := by
    intro d hd
    have : 1 < Nat.card K ^ d := Nat.one_lt_pow (hdpos d hd).ne' (by omega)
    omega
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp hp3 hpq).1,
    prod_map_ordProj_eq_three (by omega) hord (by decide) hd₁ hd₂ hd₃ h12 h13 h23 hrest,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₁ hd₁) hfac₁ hR₁,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₂ hd₂) hfac₂ hR₂,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₃ hd₃) hfac₃ hR₃]

theorem e6Three_ordProj (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (h : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1) :
    p ^ (Nat.card (adjointGroup .E6 K)).factorization p =
      p ^ (((Nat.card K ^ 2 + Nat.card K + 1) ^ 3 : ℕ)).factorization p := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  obtain ⟨hpq, hord, hx, hq1, -, hQ2, hQ3, hQ4, hQ5⟩ := e6Three_data hp hp3 h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set n₀ : ℕ := q ^ 2 + q + 1 with hn₀def
  have hn₀ : n₀ ≠ 0 := Nat.succ_ne_zero _
  have hn₀Z : (n₀ : ℤ) = (q : ℤ) ^ 2 + (q : ℤ) + 1 := by
    rw [hn₀def]
    push_cast
    ring
  have hnd : ∀ y : ℤ, (y : ZMod p) ≠ 0 → ¬ (p : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 hd)
  have hc1 : ¬ (p : ℤ) ∣ (q : ℤ) - 1 := hq1
  have hc3 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 3 + 1 := hnd _ (by push_cast; exact hQ3)
  have hc4 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 6 + (q : ℤ) ^ 3 + 1 := hnd _ (by push_cast; exact hQ4)
  have hc5 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 6 + 1 := hnd _ (by push_cast; exact hQ5)
  have hR1 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) := hpz.not_dvd_mul hc1 hc3
  have hR2 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) ^ 6 + (q : ℤ) ^ 3 + 1) :=
    hpz.not_dvd_mul hc1 hc4
  have hR3 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 6 + 1) :=
    hpz.not_dvd_mul hR1 hc5
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hrest : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), d ≠ 6 → d ≠ 9 → d ≠ 12 → ¬ 3 ∣ d := by
    intro d hd h6 h9 h12
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have key := ordProj_card_adjointGroup_E6_three (K := K) (p := p) (m := 3) (d₁ := 6) (d₂ := 9)
    (d₃ := 12) (n₀ := n₀) (R₁ := ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1))
    (R₂ := ((q : ℤ) - 1) * ((q : ℤ) ^ 6 + (q : ℤ) ^ 3 + 1))
    (R₃ := ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 6 + 1))
    hp hp3 hpq hord (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hrest
    hn₀ (by rw [hcast, hn₀Z]; ring) hR1 (by rw [hcast, hn₀Z]; ring) hR2
    (by rw [hcast, hn₀Z]; ring) hR3
  have hordN : ordProj[p] (n₀ ^ 3) = ordProj[p] n₀ * ordProj[p] n₀ * ordProj[p] n₀ := by
    rw [pow_succ, pow_succ, pow_one, Nat.ordProj_mul p (mul_ne_zero hn₀ hn₀) hn₀,
      Nat.ordProj_mul p hn₀ hn₀]
  rw [key]
  exact hordN.symm

end CFSG.RankThree.PartOne.KE6
