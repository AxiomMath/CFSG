module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFF3
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TE
public import CFSG.Quasithin.EmptyFaithful.T1521SCutComp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpModels
public import CFSG.Quasithin.Vol2.Ch3Sec3Obs3324
public import CFSG.Quasithin.Vol2.Ch11SecO8A

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

private theorem exp_lt_of_two_pow_dvd {n : ℕ} (h : 2 ^ n ∣ 17971200) : n < 25 := by
  by_contra hc
  have hc' : 25 ≤ n := by omega
  have h1 : 2 ^ 25 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc'
  have h2 : 2 ^ n ≤ 17971200 := Nat.le_of_dvd (by norm_num) h
  have h3 : (2 : ℕ) ^ 25 = 33554432 := by norm_num
  omega

private theorem sl2_order_ne (n : ℕ) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 17971200 := by
  intro h
  have hd : 2 ^ n ∣ 17971200 := ⟨(2 ^ n) ^ 2 - 1, h.symm⟩
  have hn := exp_lt_of_two_pow_dvd hd
  interval_cases n <;> norm_num at h

private theorem sl3_order_ne (n : ℕ) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ 17971200 := by
  intro h
  have hd : 2 ^ n ∣ 17971200 :=
    ⟨(2 ^ n) ^ 2 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)), by rw [← h]; ring⟩
  have hn := exp_lt_of_two_pow_dvd hd
  interval_cases n <;> norm_num at h

private theorem sp4_order_ne {n : ℕ} (hn2 : 2 ≤ n) :
    (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) ≠ 17971200 := by
  intro h
  have hd : 2 ^ n ∣ 17971200 :=
    ⟨(2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)), by rw [← h]; ring⟩
  have hn := exp_lt_of_two_pow_dvd hd
  interval_cases n <;> norm_num at h

private theorem g2_order_ne {n : ℕ} (hn2 : 2 ≤ n) :
    (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ 17971200 := by
  intro h
  have hd : 2 ^ n ∣ 17971200 :=
    ⟨(2 ^ n) ^ 5 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)), by rw [← h]; ring⟩
  have hn := exp_lt_of_two_pow_dvd hd
  interval_cases n <;> norm_num at h

private theorem one_le_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hc : Nat.card K = 2 ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · have h1 := Finite.one_lt_card (α := K)
    rw [hc, h0, pow_zero] at h1
    exact absurd h1 (lt_irrefl 1)
  · exact h0

private theorem commutator_subgroup_le_self {G : Type} [Group G] (H : Subgroup G) :
    ⁅H, H⁆ ≤ H := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)) (H.inv_mem hh)

section TitsNotB55


theorem titsNotB55Fact_holds : FFStep.TitsNotB55Fact := by
  intro Y X _ _ hY hXY hB
  obtain ⟨e⟩ := hXY
  have hX : Nat.card X = 17971200 :=
    (Nat.card_congr e.toEquiv).trans (CFSG.Quasithin.T1521SCut.card_isTits hY)
  rcases hB with ⟨n, K, hF, hfin, hc, ⟨f⟩⟩ | ⟨n, K, hF, hfin, hc, ⟨f⟩⟩ |
    ⟨n, K, hF, hfin, hc, ⟨f⟩⟩ | ⟨n, K, hF, hfin, hc, ⟨f⟩⟩ | h5 | h6 | h7 | h8
  · have h1 := (Nat.card_congr f.toEquiv).symm.trans hX
    rw [CFSG.Open.StatedAPI.card_statedSL_two K, hc] at h1
    exact sl2_order_ne n h1
  · have h1 := (Nat.card_congr f.toEquiv).symm.trans hX
    rw [CFSG.Open.StatedAPI.card_statedSL_three K, hc] at h1
    exact sl3_order_ne n h1
  · have h1 := (Nat.card_congr f.toEquiv).symm.trans hX
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by
        have := one_le_of_card_eq_two_pow hc
        omega
      have hK2 : Nat.card K = 2 := hc.trans (by norm_num)
      have hSp : Nat.card (StatedSp 2 K) = 720 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two K, hK2] <;>
          norm_num
      haveI : Finite ↥(StatedSp 2 K) := Nat.finite_of_card_ne_zero (by simp [hSp])
      have hcard := Subgroup.card_le_of_le (commutator_subgroup_le_self (StatedSp 2 K))
      rw [h1, hSp] at hcard
      omega
    · have h4 : 4 ≤ Nat.card K := by
        rw [hc]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
      have hperf : Group.IsPerfect ↥(StatedSp 2 K) :=
        Group.isPerfect_def.mpr (CFSG.ComponentClassification.CatFC.commutator_statedSp_eq_top
          (k := K) (m := 2) (by norm_num) (Or.inl h4))
      rw [Subgroup.isPerfect_iff.mp hperf,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two K, hc] at h1
      exact sp4_order_ne hge h1
  · have h1 := (Nat.card_congr f.toEquiv).symm.trans hX
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by
        have := one_le_of_card_eq_two_pow hc
        omega
      have hG : Nat.card (CFSG.Open.quasithinG2 K) = 12096 := by
        rw [CFSG.Quasithin.Vol2.Ch11.SecC.O8.card_quasithinG2 hc, hc] <;> norm_num
      haveI : Finite ↥(CFSG.Open.quasithinG2 K) := Nat.finite_of_card_ne_zero (by simp [hG])
      have hcard := Subgroup.card_le_of_le (commutator_subgroup_le_self (CFSG.Open.quasithinG2 K))
      rw [h1, hG] at hcard
      omega
    · rw [CFSG.Quasithin.H13.Obs3324.commutator_quasithinG2_eq (by omega) hc,
        CFSG.Quasithin.Vol2.Ch11.SecC.O8.card_quasithinG2 hc, hc] at h1
      exact g2_order_ne hge h1
  · have h5' : Nonempty (X ≃* alternatingGroup (Fin 7)) := h5
    obtain ⟨f⟩ := h5'
    have h1 := (Nat.card_congr f.toEquiv).symm.trans hX
    rw [nat_card_alternatingGroup, Nat.card_fin] at h1
    norm_num [Nat.factorial] at h1
  · have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_fin] <;> norm_num [Nat.factorial]
    have h1 := CFSG.Quasithin.Vol2.Ch11.SecC.O8.card_of_isHat h6 h360
    omega
  · obtain ⟨f⟩ := h7
    have h1 := (Nat.card_congr f.toEquiv).symm.trans hX
    rw [CFSG.Open.StatedAPI.card_statedSL_four_zmod_two] at h1
    omega
  · obtain ⟨f⟩ := h8
    have h1 := (Nat.card_congr f.toEquiv).symm.trans hX
    rw [CFSG.Open.StatedAPI.card_statedSL_five_zmod_two] at h1
    omega

end TitsNotB55

section FFStepHolds


theorem ffCentralizerFact_holds
    : FFCentralizerFact :=
  ffCentralizerFact_of CFSG.Quasithin.H13.titsBasicFact_holds CFSG.ASVolI.as_B_5_5
    titsNotB55Fact_holds

end FFStepHolds

end CFSG.Quasithin.H13.T614

end
