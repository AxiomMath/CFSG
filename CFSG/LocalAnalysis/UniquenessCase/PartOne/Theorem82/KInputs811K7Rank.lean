module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.GroupTheory.WeirSylow.CrossRankUnitary
import CFSG.GroupTheory.WeirSylow.CrossRankForms
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.GroupTheory.WeirSylow

namespace K7Rank

section Arithmetic

private theorem qPlusPi_dvd_sq_sub_one (r f : ℕ) : qPlusPi r f ∣ (r ^ f) ^ 2 - 1 := by
  unfold qPlusPi
  split_ifs with h
  · obtain ⟨m, hm⟩ : ∃ m, r ^ f = m + 1 := ⟨r ^ f - 1, by omega⟩
    rw [hm]
    refine ⟨m, ?_⟩
    apply Nat.sub_eq_of_eq_add
    ring
  · simpa using Nat.sub_dvd_pow_sub_pow (r ^ f) 1 2

private theorem qPlusPi_eq_add_one {r f : ℕ} (h : r ^ f % 3 = 1) : qPlusPi r f = r ^ f + 1 := by
  unfold qPlusPi
  rw [if_pos h]

private theorem qPlusPi_eq_sub_one {r f : ℕ} (h : r ^ f % 3 = 2) : qPlusPi r f = r ^ f - 1 := by
  unfold qPlusPi
  rw [if_neg (by omega)]

end Arithmetic

section Models

variable {X : Type} [Group X] [Finite X] {p n r f : ℕ} [Fact p.Prime]

private theorem pRank_le_div_two_of_psl (hp : Odd p) (hpn : ¬ p ∣ n) (hpq : p ∣ r ^ f + 1)
    (h : StatedClassicalModel X .PSL n r f) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ n / 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e]
  exact pRank_top_statedProj_statedSL_le_div_two hp hpn (by rwa [hK])

private theorem pRank_le_div_two_of_psu (hp : Odd p) (hpn : ¬ p ∣ n) (hpq : p ∣ r ^ f - 1)
    (h : StatedClassicalModel X .PSU n r f) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ n / 2 := by
  obtain ⟨-, L, _, _, hL, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e]
  exact pRank_top_statedProj_statedSU_le_div_two hp hL hpn hpq

private theorem pRank_eq_of_psp (hp : Odd p) (hpq : p ∣ (r ^ f) ^ 2 - 1) (hn : 1 ≤ n)
    (h : StatedClassicalModel X .PSp n r f) : CFSG.Open.pRank p (⊤ : Subgroup X) = n := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e]
  exact pRank_top_statedProj_statedSp_eq_of_dvd hp (by rwa [hK]) hn

private theorem pRank_le_of_pOmegaOdd (hp : Odd p) (hr : Odd (r ^ f)) (hpq : p ∣ (r ^ f) ^ 2 - 1)
    (h : StatedClassicalModel X .POmegaOdd n r f) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ n := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e]
  exact pRank_top_statedProj_statedOmega_quadOdd_le_of_dvd hp (by rwa [hK]) (by rwa [hK]) n

private theorem pRank_top_statedProj_le_two {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] (hp : Odd p) (hpK : ¬ p ∣ Nat.card K)
    (hpK2 : ¬ p ∣ Nat.card K ^ 2 - 1) (hι : Fintype.card ι ≤ 8) (H : Subgroup (GL ι K)) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) ≤ 2 :=
  (pRank_top_statedProj_le_card_div_three hp hpK hpK2 H).trans (by omega)

private theorem pRank_le_two_of_psl (hp : Odd p) (hpq : ¬ p ∣ r ^ f)
    (hpq2 : ¬ p ∣ (r ^ f) ^ 2 - 1) (hn : n ≤ 8) (h : StatedClassicalModel X .PSL n r f) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e]
  exact pRank_top_statedProj_le_two hp (by rwa [hK]) (by rwa [hK]) (by simpa using hn) _

private theorem pRank_le_two_of_psu (hp : Odd p) (hpq : ¬ p ∣ r ^ f)
    (hpq2 : ¬ p ∣ (r ^ f) ^ 2 - 1) (hn1 : 1 ≤ n) (hn : n ≤ 8)
    (h : StatedClassicalModel X .PSU n r f) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨-, L, _, _, hL, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e]
  exact (pRank_top_statedProj_statedSU_le_div_three hp hL hpq hpq2 hn1).trans (by omega)

private theorem pRank_le_two_of_psp (hp : Odd p) (hpq : ¬ p ∣ r ^ f)
    (hpq2 : ¬ p ∣ (r ^ f) ^ 2 - 1) (hn : n ≤ 4) (h : StatedClassicalModel X .PSp n r f) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e]
  exact pRank_top_statedProj_le_two hp (by rwa [hK]) (by rwa [hK]) (by simp; omega) _

private theorem pRank_le_two_of_pOmegaOdd (hp : Odd p) (hpq : ¬ p ∣ r ^ f)
    (hpq2 : ¬ p ∣ (r ^ f) ^ 2 - 1) (hn : n ≤ 3) (h : StatedClassicalModel X .POmegaOdd n r f) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e]
  exact pRank_top_statedProj_le_two hp (by rwa [hK]) (by rwa [hK]) (by simp; omega) _

private theorem pRank_le_two_of_pOmegaMinus (hp : Odd p) (hpq : ¬ p ∣ r ^ f)
    (hpq2 : ¬ p ∣ (r ^ f) ^ 2 - 1) (hn : n ≤ 4) (h : StatedClassicalModel X .POmegaMinus n r f) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, b, c, -, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e]
  exact pRank_top_statedProj_le_two hp (by rwa [hK]) (by rwa [hK]) (by simp; omega) _

end Models

section Quotient

private theorem pRank_le_two_of_l4 {X : Type} [Group X] [Finite X] {r f p : ℕ}
    (h : IsLieFam811 X .l4 r f) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ qPlusPi r f) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp4 : ¬ p ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  obtain ⟨-, -, ⟨h3, hm⟩ | ⟨h3, hm⟩⟩ := h
  · rw [qPlusPi_eq_add_one h3] at hpq
    have := pRank_le_div_two_of_psl hodd hp4 hpq (hm.statedClassicalModel_of_ne_zero (by norm_num))
    omega
  · rw [qPlusPi_eq_sub_one h3] at hpq
    have := pRank_le_div_two_of_psu hodd hp4 hpq (hm.statedClassicalModel_of_ne_zero (by norm_num))
    omega

private theorem pRank_le_three_of_psp6 {X : Type} [Group X] [Finite X] {r f p : ℕ}
    (h : IsLieFam811 X .psp6 r f) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ qPlusPi r f) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3 := by
  haveI := Fact.mk hp
  obtain ⟨-, -, hm⟩ := h
  exact (pRank_eq_of_psp (hp.odd_of_ne_two (by omega)) (hpq.trans (qPlusPi_dvd_sq_sub_one r f))
    (by norm_num) (hm.statedClassicalModel_of_ne_zero (by norm_num))).le

private theorem pRank_le_three_of_omega7 {X : Type} [Group X] [Finite X] {r f p : ℕ}
    (h : IsLieFam811 X .omega7 r f) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ qPlusPi r f) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3 := by
  haveI := Fact.mk hp
  obtain ⟨hr, hr2, -, hm⟩ := h
  exact pRank_le_of_pOmegaOdd (hp.odd_of_ne_two (by omega)) ((hr.odd_of_ne_two hr2).pow)
    (hpq.trans (qPlusPi_dvd_sq_sub_one r f)) (hm.statedClassicalModel_of_ne_zero (by norm_num))

private theorem pRank_le_two_of_not_dvd {X : Type} [Group X] [Finite X] {fam : LieFam811}
    {r f p : ℕ} (h : IsLieFam811 X fam r f) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ r ^ f)
    (hpq2 : ¬ p ∣ r ^ (2 * f) - 1) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  rw [pow_mul'] at hpq2
  rcases fam with _ | _ | _ | _ | _ | _
  · obtain ⟨-, -, hm⟩ := h
    exact pRank_le_two_of_psp hodd hpq hpq2 (by norm_num)
      (hm.statedClassicalModel_of_ne_zero (by norm_num))
  · obtain ⟨-, -, -, hm⟩ := h
    exact pRank_le_two_of_pOmegaOdd hodd hpq hpq2 (by norm_num)
      (hm.statedClassicalModel_of_ne_zero (by norm_num))
  · obtain ⟨-, -, hm⟩ := h
    exact pRank_le_two_of_pOmegaMinus hodd hpq hpq2 (by norm_num)
      (hm.statedClassicalModel_of_ne_zero (by norm_num))
  · obtain ⟨-, -, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := h
    · exact pRank_le_two_of_psl hodd hpq hpq2 (by norm_num)
        (hm.statedClassicalModel_of_ne_zero (by norm_num))
    · exact pRank_le_two_of_psu hodd hpq hpq2 (by norm_num) (by norm_num)
        (hm.statedClassicalModel_of_ne_zero (by norm_num))
  · obtain ⟨-, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := h
    · exact pRank_le_two_of_psl hodd hpq hpq2 (by norm_num)
        (hm.statedClassicalModel_of_ne_zero (by norm_num))
    · exact pRank_le_two_of_psu hodd hpq hpq2 (by norm_num) (by norm_num)
        (hm.statedClassicalModel_of_ne_zero (by norm_num))
  · obtain ⟨-, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := h
    · exact pRank_le_two_of_psl hodd hpq hpq2 (by norm_num)
        (hm.statedClassicalModel_of_ne_zero (by norm_num))
    · exact pRank_le_two_of_psu hodd hpq hpq2 (by norm_num) (by norm_num)
        (hm.statedClassicalModel_of_ne_zero (by norm_num))

end Quotient

private theorem pRank_top_eq_quotient_center {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (hZ : ¬ p ∣ Nat.card (center Y)) :
    CFSG.pRank p (⊤ : Subgroup Y) = CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ center Y)) := by
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_quotient_eq (center Y) hZ]

end K7Rank

theorem pRank_le_two_of_isLie811_l4
    {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hY : IsLie811 Y .l4 r f) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ qPlusPi r f) : CFSG.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  haveI := Fact.mk hp
  have hZ : center Y = ⊥ :=
    center_eq_bot_of_isLie811_of_ne hY (by decide) fun h => absurd h (by decide)
  obtain ⟨-, -, hX⟩ := hY
  rw [K7Rank.pRank_top_eq_quotient_center (by rw [hZ, Subgroup.card_bot]; exact hp.not_dvd_one)]
  exact K7Rank.pRank_le_two_of_l4 hX hp hp5 hpq

theorem pRank_le_three_of_isLie811_psp6_omega7
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (hY : IsLie811 Y fam r f)
    (hfam : fam = .psp6 ∨ fam = .omega7) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ qPlusPi r f) : CFSG.pRank p (⊤ : Subgroup Y) ≤ 3 := by
  haveI := Fact.mk hp
  have hne : fam ≠ .l7 := by rcases hfam with rfl | rfl <;> decide
  have hsp : fam = .psp6 → r ^ f ≠ 2 := by
    rintro - hq
    rw [K7Rank.qPlusPi_eq_sub_one (by simp [hq]), hq] at hpq
    exact hp.ne_one (by simpa using hpq)
  have hZ : center Y = ⊥ := center_eq_bot_of_isLie811_of_ne hY hne hsp
  obtain ⟨-, -, hX⟩ := hY
  rw [K7Rank.pRank_top_eq_quotient_center (by rw [hZ, Subgroup.card_bot]; exact hp.not_dvd_one)]
  rcases hfam with rfl | rfl
  · exact K7Rank.pRank_le_three_of_psp6 hX hp hp5 hpq
  · exact K7Rank.pRank_le_three_of_omega7 hX hp hp5 hpq

theorem pRank_le_two_of_isLie811_of_not_dvd
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (hY : IsLie811 Y fam r f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ r ^ f * (r ^ (2 * f) - 1)) :
    CFSG.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  haveI := Fact.mk hp
  have h1 : ¬ p ∣ r ^ f := fun h => hpq (h.mul_right _)
  have h2 : ¬ p ∣ r ^ (2 * f) - 1 := fun h => hpq (h.mul_left _)
  have hZ : ¬ p ∣ Nat.card (center Y) := by
    rcases eq_or_ne fam .l7 with rfl | hne
    · intro hd
      apply h2
      rw [pow_mul']
      exact ((hd.trans (card_center_dvd_of_isLie811_l7 hY)).trans (Nat.gcd_dvd_right _ _)).trans
        (K7Rank.qPlusPi_dvd_sq_sub_one r f)
    · rw [center_eq_bot_of_isLie811 hY hne, Subgroup.card_bot]
      exact hp.not_dvd_one
  obtain ⟨-, -, hX⟩ := hY
  rw [K7Rank.pRank_top_eq_quotient_center hZ]
  exact K7Rank.pRank_le_two_of_not_dvd hX hp hp5 h1 h2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
