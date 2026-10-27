module

public import CFSG.Quasithin.Vol2.Ch11SecO7l
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem not_T_fix {L : Type} [Group L] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (N : ℕ)
    (hN : Nat.card L = N) (hN0 : N ≠ 0)
    (hchk : ∀ q ∈ N.primeFactorsList, 7 ≤ q → q ^ 2 ∣ N → TOrderNe q N) : ¬ InT p L :=
  not_T_of_card' hN hN0 hchk p hp hp7

theorem a312A5_c9 {Y : Type} [Group Y] {B L : Subgroup Y} {p a : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hBa : Nat.card ↥B = 2 ^ a * 15) (h : A312C9 B L) : ¬ InT p ↥L := by
  have hU : IsPSU 3 5 1 ↥L → ¬ InT p ↥L := fun hL => not_T_fix hp hp7 126000
    (card_of_isPSU35 hL) (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide)
  have hSU : IsSU3 5 ↥L → ¬ InT p ↥L := fun hL => not_T_fix hp hp7 378000
    (card_of_isSU35 hL) (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide)
  have hL5 : Nat.card ↥L = 372000 → ¬ InT p ↥L := fun hc => not_T_fix hp hp7 372000 hc
    (by norm_num) (by simp only [Nat.primeFactorsList_ofNat]; decide)
  rcases h with ⟨s, r, hr, hr3, ⟨e⟩, hL⟩ | ⟨-, hL⟩ | ⟨-, hL⟩
  · have : Fact r.Prime := ⟨hr⟩
    have hrB : r ∣ Nat.card ↥B := by
      rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
      exact dvd_mul_right r _
    rcases eq_three_or_five hr (by omega) (hBa ▸ hrB) with rfl | rfl
    · omega
    · cases s
      · rcases hL with hL | hL
        · exact hU hL
        · exact hSU hL
      · rcases hL with hL | hL
        · exact hL5 (H13.NotLie.card_psl35 hL)
        · exact hL5 (card_of_isSL35 hL)
  · exact hU hL
  · exact hSU hL


theorem a312A5_c2 {Y : Type} [Group Y] [Finite Y] {B L : Subgroup Y} {p c : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hMc : Nat.card (ModO2 B) = 2 ^ c * 15) (h : A312C2 B L) : ¬ InT p ↥L := by
  obtain ⟨⟨n, hn⟩, hL, P, hP, hBP⟩ := h
  obtain ⟨hn1, hcn⟩ := SecA.C10KH.card_of_isPSL_two_two hn
  have hodd : Odd ((2 ^ n) ^ 2 - 1) :=
    CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hn1 (by norm_num)
  have h1 : 2 ^ n * ((2 ^ n) ^ 2 - 1) = 2 ^ c * 15 := hcn.symm.trans hMc
  have h2 := SecA.eq_of_two_pow_mul_odd hodd ⟨7, rfl⟩ h1
  subst h2
  have h3 : (2 ^ n) ^ 2 - 1 = 15 :=
    Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ n) h1
  have h4 : (2 ^ n) ^ 2 = (2 ^ 2) ^ 2 := by
    have : (2 ^ 2) ^ 2 = 16 := by norm_num
    omega
  have hn2 : n = 2 := Nat.pow_right_injective le_rfl (Nat.pow_left_injective two_ne_zero h4)
  subst hn2
  rw [hBP] at hn
  rcases SecA.factL2Parabolic_holds Y L P 2 le_rfl hL hP hn with h | h | h | h | h | h | ⟨h3, -⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
    refine not_T_fix hp hp7 60480 ?_ (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide)
    rw [Nat.card_congr (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
      3 K).symm).toEquiv, CFSG.OrderReductions.LinearOrders.card_specialLinear K 3
      (by norm_num), hK]
    decide
  · exact not_T_fix hp hp7 20160 (card_of_isPSL322 h) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide)
  · refine not_T_fix hp hp7 979200 ?_ (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide)
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl, ordBC]
    decide
  · refine not_T_fix hp hp7 251596800 ?_ (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide)
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 h.2, ordG2]
    norm_num
  · refine not_T_fix hp hp7 3417910227763200 ?_ (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h, ordTwistedF4]
    norm_num
  · refine not_T_fix hp hp7 67802350642790400 ?_ (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two
      (by norm_num) h.2, ordTrialityD4]
    norm_num
  · exact absurd h3 (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
