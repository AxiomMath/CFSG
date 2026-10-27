module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

namespace CFSG.StandardType

namespace ExcE6Plus

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

private theorem ggKGE6c_geomSum_2_1 (q : ℕ) : geomSum 2 1 q = q + 1 := by
  simp [geomSum, Finset.sum_range_succ]; ring

private theorem ggKGE6c_geomSum_3_1 (q : ℕ) : geomSum 3 1 q = q ^ 2 + q + 1 := by
  simp [geomSum, Finset.sum_range_succ]; ring

private theorem ggKGE6c_geomSum_4_1 (q : ℕ) : geomSum 4 1 q = (q + 1) * (q ^ 2 + 1) := by
  simp [geomSum, Finset.sum_range_succ]; ring

private theorem ggKGE6c_geomSum_5_1 (q : ℕ) :
    geomSum 5 1 q = q ^ 4 + q ^ 3 + q ^ 2 + q + 1 := by
  simp [geomSum, Finset.sum_range_succ]; ring

private theorem ggKGE6c_geomSum_2_3 (q : ℕ) : geomSum 2 3 q = q ^ 3 + 1 := by
  simp [geomSum, Finset.sum_range_succ]; ring

private theorem ggKGE6c_geomSum_8_1 (q : ℕ) :
    geomSum 8 1 q = (q + 1) * (q ^ 2 + 1) * (q ^ 4 + 1) := by
  simp [geomSum, Finset.sum_range_succ]; ring

private theorem ggKGE6c_geomSum_9_1 (q : ℕ) :
    geomSum 9 1 q = q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1 := by
  simp [geomSum, Finset.sum_range_succ]; ring

private theorem ggKGE6c_geomSum_3_4 (q : ℕ) : geomSum 3 4 q = q ^ 8 + q ^ 4 + 1 := by
  simp [geomSum, Finset.sum_range_succ]; ring

private def ggKGE6c_V (q : ℕ) : ℕ :=
  (q ^ 2 + q + 1) * (q ^ 2 + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * (q ^ 2 + 1) * (q ^ 4 + 1)
    * (q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * (q ^ 8 + q ^ 4 + 1)

private theorem ggKGE6c_prodE6_eq (q : ℕ) :
    TableBExc.prodE6 q = (q + 1) ^ 3 * (q ^ 3 + 1) * ggKGE6c_V q := by
  simp only [TableBExc.prodE6, ggKGE6c_V, ggKGE6c_geomSum_2_1, ggKGE6c_geomSum_3_1,
    ggKGE6c_geomSum_4_1, ggKGE6c_geomSum_5_1, ggKGE6c_geomSum_2_3,
    ggKGE6c_geomSum_8_1, ggKGE6c_geomSum_9_1, ggKGE6c_geomSum_3_4]
  ring

private theorem ggKGE6c_prodE6_ne_zero (q : ℕ) : TableBExc.prodE6 q ≠ 0 := by
  rw [ggKGE6c_prodE6_eq]; unfold ggKGE6c_V; positivity

private theorem ggKGE6c_not_dvd_V {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {q : ℕ}
    (hpq : p ∣ q + 1) : ¬ p ∣ ggKGE6c_V q := by
  have h24 : (24 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((24 : ℕ) : ZMod p) = 0 := h
    have hd : p ∣ 24 := (ZMod.natCast_eq_zero_iff 24 p).mp h'
    have h24e : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h24e] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
      omega
  have hq : ((q : ZMod p)) = -1 := by
    have h : ((q + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hpq
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  intro hd
  have hV : (((ggKGE6c_V q) : ℕ) : ZMod p) ≠ 0 := by
    unfold ggKGE6c_V
    push_cast
    rw [hq]
    norm_num
    exact h24
  exact hV ((ZMod.natCast_eq_zero_iff _ _).mpr hd)

private theorem ggKGE6c_padicValNat_prodE6 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {q : ℕ} (hq1 : 1 ≤ q) (hpq : p ∣ q + 1) :
    padicValNat p (TableBExc.prodE6 q) = 4 * padicValNat p (q + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hd
    have h1 : p ∣ (q + 1) - q := Nat.dvd_sub hpq hd
    have : (q + 1) - q = 1 := by omega
    rw [this] at h1
    exact hp.not_dvd_one h1
  have hp_not_dvd_3 : ¬ p ∣ 3 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    omega
  have hV := ggKGE6c_not_dvd_V hp hp5 hpq
  have hpow : padicValNat p ((q + 1) ^ 3) = 3 * padicValNat p (q + 1) :=
    padicValNat.pow (q + 1) 3
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact Nat.odd_iff.mpr h
  have hpow3 : padicValNat p (q ^ 3 + 1) = padicValNat p (q + 1) + padicValNat p 3 := by
    have := padicValNat.pow_add_pow (p := p) (x := q) (y := 1) hpodd hpq hp_not_dvd_q
      (n := 3) (by norm_num)
    simpa using this
  rw [ggKGE6c_prodE6_eq]
  calc padicValNat p ((q + 1) ^ 3 * (q ^ 3 + 1) * ggKGE6c_V q)
      = padicValNat p ((q + 1) ^ 3 * (q ^ 3 + 1)) + padicValNat p (ggKGE6c_V q) :=
        padicValNat.mul (by positivity) (fun h => hV (h ▸ dvd_zero p))
    _ = padicValNat p ((q + 1) ^ 3) + padicValNat p (q ^ 3 + 1) + padicValNat p (ggKGE6c_V q) := by
        rw [padicValNat.mul (by positivity) (by positivity)]
    _ = 3 * padicValNat p (q + 1) + (padicValNat p (q + 1) + padicValNat p 3) + 0 := by
        rw [hpow, hpow3, padicValNat.eq_zero_of_not_dvd hV]
    _ = 4 * padicValNat p (q + 1) := by
        rw [padicValNat.eq_zero_of_not_dvd hp_not_dvd_3]; ring

theorem padicValNat_card_adjointGroup
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    padicValNat p (Nat.card (adjointGroup .E6 K)) = 4 * padicValNat p (Nat.card K + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hHdvd : Nat.card (torusGroup .E6 K) ∣ (Nat.card K - 1) ^ 6 :=
    (CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E6 (K := K)) ▸ dvd_mul_right _ _
  have hp_not_dvd_qminus1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have h2 : p ∣ 2 := by
      have : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
      rwa [this] at h3
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    omega
  have hp_not_dvd_q : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ (Nat.card K + 1) - Nat.card K := Nat.dvd_sub hpq hd
    have : (Nat.card K + 1) - Nat.card K = 1 := by omega
    rw [this] at h1
    exact hp.not_dvd_one h1
  have hH0 : padicValNat p (Nat.card (torusGroup .E6 K)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd =>
      hp_not_dvd_qminus1 (hp.dvd_of_dvd_pow (dvd_trans hd hHdvd)))
  have hq360 : padicValNat p (Nat.card K ^ 36) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hp_not_dvd_q]
  have hprod : padicValNat p (TableBExc.prodE6 (Nat.card K)) =
      4 * padicValNat p (Nat.card K + 1) :=
    ggKGE6c_padicValNat_prodE6 hp hp5 hq1 hpq
  rw [TableBExc.card_adjointGroup_E6_eq]
  rw [padicValNat.mul (a := Nat.card (torusGroup .E6 K))
      (b := Nat.card K ^ 36 * TableBExc.prodE6 (Nat.card K))
      (Nat.card_pos.ne')
      (mul_ne_zero (pow_ne_zero 36 (Nat.card_pos.ne')) (ggKGE6c_prodE6_ne_zero _))]
  rw [padicValNat.mul (a := Nat.card K ^ 36) (b := TableBExc.prodE6 (Nat.card K))
      (pow_ne_zero 36 (Nat.card_pos.ne')) (ggKGE6c_prodE6_ne_zero _)]
  rw [hH0, hq360, hprod]
  ring

end ExcE6Plus

end CFSG.StandardType

end
