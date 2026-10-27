module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

namespace CFSG.StandardType

namespace ExcE6Split

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ggKGSo_pow_sub_one_ne_zero {q d : ℕ} (hq : 1 < q) (hd : d ≠ 0) :
    q ^ d - 1 ≠ 0 := by
  have h : 1 < q ^ d := one_lt_pow₀ hq hd
  omega

private theorem ggKGSo_padicValNat_list_prod {p : ℕ} [Fact p.Prime] (l : List ℕ)
    (h : ∀ a ∈ l, a ≠ 0) :
    padicValNat p l.prod = (l.map (padicValNat p)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a ≠ 0 := h a (by simp)
    have ht : ∀ b ∈ t, b ≠ 0 := fun b hb => h b (by simp [hb])
    have hprod : t.prod ≠ 0 := List.prod_ne_zero (fun h0 => ht 0 h0 rfl)
    rw [List.prod_cons, padicValNat.mul ha hprod, ih ht, List.map_cons, List.sum_cons]

private theorem ggKGSo_padicValNat_prodA {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 1 < q) (hpq : p ∣ q - 1) :
    padicValNat p (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1)) =
      6 * padicValNat p (q - 1) + padicValNat p 51840 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hd
    have h1 : p ∣ q - (q - 1) := Nat.dvd_sub hd hpq
    have hsub : q - (q - 1) = 1 := by omega
    rw [hsub] at h1
    exact hp.not_dvd_one h1
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact Nat.odd_iff.mpr h
  have hLTE : ∀ d : ℕ, d ≠ 0 →
      padicValNat p (q ^ d - 1) = padicValNat p (q - 1) + padicValNat p d := by
    intro d hd
    have := padicValNat.pow_sub_pow (p := p) (x := q) (y := 1) hpodd hq hpq hp_not_dvd_q hd
    simpa using this
  have h36 : padicValNat p (q ^ 36) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hp_not_dvd_q]
  have h2 : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
  have h6 : padicValNat p 6 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd
    rw [show (6 : ℕ) = 2 * 3 by norm_num] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h2' | h3'
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2'; omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'; omega)
  have h8 : padicValNat p 8 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd); omega)
  have h9 : padicValNat p 9 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd); omega)
  have h12 : padicValNat p 12 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h2' | h3'
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2'); omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'; omega)
  have h51840 : padicValNat p 51840 = padicValNat p 5 := by
    have h10368 : ¬ p ∣ 10368 := by
      have h : ¬ p ∣ 2 ^ 7 * 3 ^ 4 := by
        intro hd
        rcases (Nat.Prime.dvd_mul hp).mp hd with h2' | h3'
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2')
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3')
          omega
      rw [show (10368 : ℕ) = 2 ^ 7 * 3 ^ 4 by norm_num]
      exact h
    have hmul : padicValNat p (5 * 10368) = padicValNat p 5 + padicValNat p 10368 :=
      padicValNat.mul (by norm_num) (by norm_num)
    rw [show (51840 : ℕ) = 5 * 10368 by norm_num, hmul,
      padicValNat.eq_zero_of_not_dvd h10368, add_zero]
  have hne : ∀ a ∈ ([q ^ 36, q ^ 12 - 1, q ^ 9 - 1, q ^ 8 - 1, q ^ 6 - 1, q ^ 5 - 1,
      q ^ 2 - 1] : List ℕ), a ≠ 0 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pow_ne_zero 36 (by omega)
    · exact ggKGSo_pow_sub_one_ne_zero hq (by norm_num)
    · exact ggKGSo_pow_sub_one_ne_zero hq (by norm_num)
    · exact ggKGSo_pow_sub_one_ne_zero hq (by norm_num)
    · exact ggKGSo_pow_sub_one_ne_zero hq (by norm_num)
    · exact ggKGSo_pow_sub_one_ne_zero hq (by norm_num)
    · exact ggKGSo_pow_sub_one_ne_zero hq (by norm_num)
  have hAeq : q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) =
      ([q ^ 36, q ^ 12 - 1, q ^ 9 - 1, q ^ 8 - 1, q ^ 6 - 1, q ^ 5 - 1,
        q ^ 2 - 1] : List ℕ).prod := by
    simp only [List.prod_cons, List.prod_nil, mul_one]
    ring
  rw [hAeq, ggKGSo_padicValNat_list_prod _ hne]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [h36, hLTE 12 (by norm_num), hLTE 9 (by norm_num), hLTE 8 (by norm_num),
    hLTE 6 (by norm_num), hLTE 5 (by norm_num), hLTE 2 (by norm_num)]
  rw [h12, h9, h8, h6, h2, h51840]
  ring

theorem padicValNat_card_adjointGroup_split
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) :
    padicValNat p (Nat.card (adjointGroup .E6 K)) =
      6 * padicValNat p (Nat.card K - 1) + padicValNat p 51840 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : 1 < Nat.card K := Finite.one_lt_card
  have hp_not_dvd_three : ¬ p ∣ 3 := by
    intro h
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h
    omega
  have hp_not_dvd_gcd : ¬ p ∣ (Nat.card K - 1).gcd 3 := fun hd =>
    hp_not_dvd_three (dvd_trans hd (Nat.gcd_dvd_right _ _))
  have hg0 : (Nat.card K - 1).gcd 3 ≠ 0 :=
    (Nat.gcd_pos_of_pos_right _ (by norm_num)).ne'
  have hH := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E6 (K := K)
  have hord := CFSG.Timmesfeld.ExceptionalOrders.ordE6_mul (Nat.card K) hq1
  have hCEq : Nat.card (adjointGroup .E6 K) * (Nat.card K - 1).gcd 3 =
      Nat.card K ^ 36 * (Nat.card K ^ 12 - 1) * (Nat.card K ^ 9 - 1) *
        (Nat.card K ^ 8 - 1) * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 5 - 1) *
        (Nat.card K ^ 2 - 1) := by
    rw [TableBExc.card_adjointGroup_E6_eq]
    calc Nat.card (torusGroup .E6 K) *
            (Nat.card K ^ 36 * TableBExc.prodE6 (Nat.card K)) * (Nat.card K - 1).gcd 3
        = (Nat.card (torusGroup .E6 K) * (Nat.card K - 1).gcd 3) *
            (Nat.card K ^ 36 * TableBExc.prodE6 (Nat.card K)) := by ring
      _ = (Nat.card K - 1) ^ 6 *
            (Nat.card K ^ 36 * TableBExc.prodE6 (Nat.card K)) := by rw [hH]
      _ = (Nat.card K - 1) ^ 6 * Nat.card K ^ 36 * TableBExc.prodE6 (Nat.card K) := by ring
      _ = Nat.card K ^ 36 * (Nat.card K ^ 12 - 1) * (Nat.card K ^ 9 - 1) *
            (Nat.card K ^ 8 - 1) * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 5 - 1) *
            (Nat.card K ^ 2 - 1) := hord
  have hval : padicValNat p (Nat.card (adjointGroup .E6 K)) =
      padicValNat p (Nat.card K ^ 36 * (Nat.card K ^ 12 - 1) * (Nat.card K ^ 9 - 1) *
        (Nat.card K ^ 8 - 1) * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 5 - 1) *
        (Nat.card K ^ 2 - 1)) := by
    have hmul : padicValNat p (Nat.card (adjointGroup .E6 K) * (Nat.card K - 1).gcd 3) =
        padicValNat p (Nat.card (adjointGroup .E6 K)) +
          padicValNat p ((Nat.card K - 1).gcd 3) :=
      padicValNat.mul Nat.card_pos.ne' hg0
    rw [hCEq] at hmul
    rw [padicValNat.eq_zero_of_not_dvd hp_not_dvd_gcd, add_zero] at hmul
    exact hmul.symm
  rw [hval, ggKGSo_padicValNat_prodA hp hp5 hq2 hpq]

end ExcE6Split

end CFSG.StandardType

end
