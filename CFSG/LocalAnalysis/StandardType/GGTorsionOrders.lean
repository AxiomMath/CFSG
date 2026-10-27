module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionOrders

private theorem to_pow_sub_pos {q k : ℕ} (hq : 2 ≤ q) (hk : k ≠ 0) : 0 < q ^ k - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hk (by omega))

private theorem to_E8 (n : ℕ) (hn : 1 ≤ n) :
    17971200 ≤ CFSG.Open.ordE8 (2 ^ n) ∧ 3 ∣ CFSG.Open.ordE8 (2 ^ n) := by
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  constructor
  · have h1 : 17971200 ≤ 2 ^ 120 := by norm_num
    have h2 : 2 ^ 120 ≤ (2 ^ n) ^ 120 := Nat.pow_le_pow_left hq2 120
    have h3 : (2 ^ n) ^ 120 ≤ CFSG.Open.ordE8 (2 ^ n) := by
      rw [CFSG.Open.ordE8]
      have h30 : 0 < (2 ^ n) ^ 30 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h24 : 0 < (2 ^ n) ^ 24 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h20 : 0 < (2 ^ n) ^ 20 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h18 : 0 < (2 ^ n) ^ 18 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h14 : 0 < (2 ^ n) ^ 14 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h12 : 0 < (2 ^ n) ^ 12 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h8 : 0 < (2 ^ n) ^ 8 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h2' : 0 < (2 ^ n) ^ 2 - 1 := to_pow_sub_pos hq2 (by norm_num)
      calc (2 ^ n) ^ 120
          ≤ (2 ^ n) ^ 120 * ((2 ^ n) ^ 30 - 1) := Nat.le_mul_of_pos_right _ h30
        _ ≤ (2 ^ n) ^ 120 * ((2 ^ n) ^ 30 - 1) * ((2 ^ n) ^ 24 - 1) :=
              Nat.le_mul_of_pos_right _ h24
        _ ≤ (2 ^ n) ^ 120 * ((2 ^ n) ^ 30 - 1) * ((2 ^ n) ^ 24 - 1) *
              ((2 ^ n) ^ 20 - 1) := Nat.le_mul_of_pos_right _ h20
        _ ≤ (2 ^ n) ^ 120 * ((2 ^ n) ^ 30 - 1) * ((2 ^ n) ^ 24 - 1) *
              ((2 ^ n) ^ 20 - 1) * ((2 ^ n) ^ 18 - 1) := Nat.le_mul_of_pos_right _ h18
        _ ≤ (2 ^ n) ^ 120 * ((2 ^ n) ^ 30 - 1) * ((2 ^ n) ^ 24 - 1) *
              ((2 ^ n) ^ 20 - 1) * ((2 ^ n) ^ 18 - 1) * ((2 ^ n) ^ 14 - 1) :=
              Nat.le_mul_of_pos_right _ h14
        _ ≤ (2 ^ n) ^ 120 * ((2 ^ n) ^ 30 - 1) * ((2 ^ n) ^ 24 - 1) *
              ((2 ^ n) ^ 20 - 1) * ((2 ^ n) ^ 18 - 1) * ((2 ^ n) ^ 14 - 1) *
              ((2 ^ n) ^ 12 - 1) := Nat.le_mul_of_pos_right _ h12
        _ ≤ (2 ^ n) ^ 120 * ((2 ^ n) ^ 30 - 1) * ((2 ^ n) ^ 24 - 1) *
              ((2 ^ n) ^ 20 - 1) * ((2 ^ n) ^ 18 - 1) * ((2 ^ n) ^ 14 - 1) *
              ((2 ^ n) ^ 12 - 1) * ((2 ^ n) ^ 8 - 1) := Nat.le_mul_of_pos_right _ h8
        _ ≤ (2 ^ n) ^ 120 * ((2 ^ n) ^ 30 - 1) * ((2 ^ n) ^ 24 - 1) *
              ((2 ^ n) ^ 20 - 1) * ((2 ^ n) ^ 18 - 1) * ((2 ^ n) ^ 14 - 1) *
              ((2 ^ n) ^ 12 - 1) * ((2 ^ n) ^ 8 - 1) * ((2 ^ n) ^ 2 - 1) :=
              Nat.le_mul_of_pos_right _ h2'
    exact le_trans h1 (le_trans h2 h3)
  · have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
      have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
        rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
      rw [h4]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
    rw [CFSG.Open.ordE8]
    exact dvd_mul_of_dvd_right h3 _

private theorem to_F4 (n : ℕ) (hn : 1 ≤ n) :
    17971200 ≤ CFSG.Open.ordF4 (2 ^ n) ∧ 3 ∣ CFSG.Open.ordF4 (2 ^ n) := by
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  constructor
  · have hnum : 17971200 ≤ 2 ^ 24 * 3 := by norm_num
    have h24 : 2 ^ 24 ≤ (2 ^ n) ^ 24 := Nat.pow_le_pow_left hq2 24
    have h12 : 3 ≤ (2 ^ n) ^ 12 - 1 := by
      have h4 : 4 ≤ (2 ^ n) ^ 12 := by
        have hpow : 2 ^ 12 ≤ (2 ^ n) ^ 12 := Nat.pow_le_pow_left hq2 12
        have h412 : 4 ≤ 2 ^ 12 := by norm_num
        exact le_trans h412 hpow
      omega
    have hprod : 2 ^ 24 * 3 ≤ (2 ^ n) ^ 24 * ((2 ^ n) ^ 12 - 1) := Nat.mul_le_mul h24 h12
    have hbase : (2 ^ n) ^ 24 * ((2 ^ n) ^ 12 - 1) ≤ CFSG.Open.ordF4 (2 ^ n) := by
      rw [CFSG.Open.ordF4]
      have h8 : 0 < (2 ^ n) ^ 8 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h6 : 0 < (2 ^ n) ^ 6 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h2' : 0 < (2 ^ n) ^ 2 - 1 := to_pow_sub_pos hq2 (by norm_num)
      calc (2 ^ n) ^ 24 * ((2 ^ n) ^ 12 - 1)
          ≤ (2 ^ n) ^ 24 * ((2 ^ n) ^ 12 - 1) * ((2 ^ n) ^ 8 - 1) :=
              Nat.le_mul_of_pos_right _ h8
        _ ≤ (2 ^ n) ^ 24 * ((2 ^ n) ^ 12 - 1) * ((2 ^ n) ^ 8 - 1) *
              ((2 ^ n) ^ 6 - 1) := Nat.le_mul_of_pos_right _ h6
        _ ≤ (2 ^ n) ^ 24 * ((2 ^ n) ^ 12 - 1) * ((2 ^ n) ^ 8 - 1) *
              ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) := Nat.le_mul_of_pos_right _ h2'
    exact le_trans hnum (le_trans hprod hbase)
  · have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
      have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
        rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
      rw [h4]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
    rw [CFSG.Open.ordF4]
    exact dvd_mul_of_dvd_right h3 _

private theorem to_twF4 (n : ℕ) (hn : 3 ≤ n) :
    17971200 ≤ CFSG.Open.ordTwistedF4 (2 ^ n) ∧ 3 ∣ CFSG.Open.ordTwistedF4 (2 ^ n) := by
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  constructor
  · have hnum : 17971200 ≤ 8 ^ 12 := by norm_num
    have hpow : 8 ^ 12 ≤ (2 ^ n) ^ 12 := Nat.pow_le_pow_left hq8 12
    have hbase : (2 ^ n) ^ 12 ≤ CFSG.Open.ordTwistedF4 (2 ^ n) := by
      rw [CFSG.Open.ordTwistedF4]
      have h1 : 0 < (2 ^ n) ^ 6 + 1 := by positivity
      have h2 : 0 < (2 ^ n) ^ 4 - 1 := to_pow_sub_pos hq2 (by norm_num)
      have h3 : 0 < (2 ^ n) ^ 3 + 1 := by positivity
      have h4 : 0 < 2 ^ n - 1 := by omega
      calc (2 ^ n) ^ 12
          ≤ (2 ^ n) ^ 12 * ((2 ^ n) ^ 6 + 1) := Nat.le_mul_of_pos_right _ h1
        _ ≤ (2 ^ n) ^ 12 * ((2 ^ n) ^ 6 + 1) * ((2 ^ n) ^ 4 - 1) :=
              Nat.le_mul_of_pos_right _ h2
        _ ≤ (2 ^ n) ^ 12 * ((2 ^ n) ^ 6 + 1) * ((2 ^ n) ^ 4 - 1) *
              ((2 ^ n) ^ 3 + 1) := Nat.le_mul_of_pos_right _ h3
        _ ≤ (2 ^ n) ^ 12 * ((2 ^ n) ^ 6 + 1) * ((2 ^ n) ^ 4 - 1) *
              ((2 ^ n) ^ 3 + 1) * (2 ^ n - 1) := Nat.le_mul_of_pos_right _ h4
    exact le_trans hnum (le_trans hpow hbase)
  · have h3 : 3 ∣ (2 ^ n) ^ 4 - 1 := by
      have h4 : (2 ^ n) ^ 4 = 16 ^ n := by
        rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, Nat.mul_comm]
      rw [h4]
      exact dvd_trans (by norm_num : (3 : ℕ) ∣ 15) (by simpa using Nat.sub_dvd_pow_sub_pow 16 1 n)
    rw [CFSG.Open.ordTwistedF4]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right h3 ((2 ^ n) ^ 12 * ((2 ^ n) ^ 6 + 1)))
        ((2 ^ n) ^ 3 + 1))
      (2 ^ n - 1)

private theorem to_ordTits : 17971200 ≤ CFSG.Open.ordTits ∧ 3 ∣ CFSG.Open.ordTits := by
  constructor <;> norm_num [CFSG.Open.ordTits]

theorem ggTorsion_marking_card
    {J : Type} [Group J]
    (h : LargeEvenMarking J fun lab _ _ _ _ _ => GGL45TorsionTag lab) :
    17971200 ≤ Nat.card (J ⧸ Subgroup.center J) ∧ 3 ∣ Nat.card (J ⧸ Subgroup.center J) := by
  obtain ⟨lab, hlab, R, _hRgrp, I, F, θ, _hsimple, _hna, hP, hM⟩ :=
    largeEvenMarking_exists_markedModel h
  have hcard : Nat.card (J ⧸ Subgroup.center J) = Nat.card R := Nat.card_congr θ.toEquiv
  obtain ⟨t, l, n⟩ := lab
  have hP' : t = .E8 ∨ t = .F4 ∨ t = .twF4 ∨ t = .twF4der := by
    simpa only [GGL45TorsionTag] using hP
  rcases hP' with rfl | rfl | rfl | rfl
  · dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordE8 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    obtain ⟨hge, hdiv⟩ := to_E8 n hn
    refine ⟨?_, ?_⟩
    · rw [hcard, hR]; exact hge
    · rw [hcard, hR]; exact hdiv
  · dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordF4 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    obtain ⟨hge, hdiv⟩ := to_F4 n hn
    refine ⟨?_, ?_⟩
    · rw [hcard, hR]; exact hge
    · rw [hcard, hR]; exact hdiv
  · dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, -, hn⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordTwistedF4 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    obtain ⟨hge, hdiv⟩ := to_twF4 n hn
    refine ⟨?_, ?_⟩
    · rw [hcard, hR]; exact hge
    · rw [hcard, hR]; exact hdiv
  · dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, -⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordTits :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    obtain ⟨hge, hdiv⟩ := to_ordTits
    refine ⟨?_, ?_⟩
    · rw [hcard, hR]; exact hge
    · rw [hcard, hR]; exact hdiv

end TorsionOrders

end CFSG.StandardType
