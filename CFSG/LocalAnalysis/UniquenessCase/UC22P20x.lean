module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20w
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevResCore
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevResMain
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

section Table


theorem uc22p20x_lieOddRankChev (hG : CFSG.Open.GriessAllModelsStatement) : LieOddRankChev :=
  lieOddRankChev_of_res hG
    (lieOddRankChevRes_of_core hG ⟨lieOddRankChevLinCore_holds hG, lieOddRankChevUniCore_holds hG⟩)

end Table

section Excl

variable {K : Type} [Group K] [Finite K]

theorem uc22p20x_excl_three (h : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) :=
  ⟨3, Nat.prime_three, by norm_num, Or.inl ⟨rfl, uc22p20r_rankWit_of_le_pRank Nat.prime_three h⟩⟩

theorem uc22p20x_excl_borel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)) (hB : uc22p20oBorelWit K p 2) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) :=
  ⟨p, hp, hp2, Or.inr ⟨uc22p20r_rankWit_of_le_pRank hp h, hB⟩⟩

theorem uc22p20x_excl_psl (hT : LieOddRankChev) (hres : uc22p20vExclRes)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m n : ℕ} (hm : 5 ≤ m)
    (hn : 2 < n) (hM : LieModel (K ⧸ center K) .PSL m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSL m 2 n := hM.statedClassicalModel (by decide)
  by_cases hcase : Even n ∨ 8 ≤ m
  · refine uc22p20x_excl_three ?_
    rw [uc22p20w_pRank_psl hT hq hS (by omega) (by omega) Nat.prime_three (by norm_num)]
    by_cases hev : Even n
    · exact uc22p20v_four_le_rkLin_true_one Nat.prime_three
        (by rw [uc22p20v_eP_three, if_pos hev]) hm (fun _ => by norm_num)
    · exact uc22p20v_four_le_rkLin_true_two (by rw [uc22p20v_eP_three, if_neg hev])
        (hcase.resolve_left hev)
  · obtain ⟨hnodd, hm8⟩ := not_or.1 hcase
    have hodd' : Odd n := Nat.not_even_iff_odd.1 hnodd
    obtain ⟨p, hp, hpd⟩ := uc22p20v_exists_prime_dvd_sub_one (by omega : 2 ≤ n)
    have hp2 := uc22p20v_ne_two_of_dvd_sub_one (by omega) hp hpd
    refine uc22p20x_excl_borel hp hp2 ?_ (hres.lin K hq hodd m n (by omega) hn hodd' hM p hp hpd)
    rw [uc22p20w_pRank_psl hT hq hS (by omega) (by omega) hp hp2]
    exact uc22p20v_four_le_rkLin_true_one hp (uc22p20v_eP_of_dvd hpd) hm
      (fun _ hp5 => uc22p20v_not_five_dvd_sub_one hodd' (hp5 ▸ hpd))

theorem uc22p20x_excl_psu (hT : LieOddRankChev) (hres : uc22p20vExclRes)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m n : ℕ} (hm : 5 ≤ m)
    (hn : 2 < n) (hM : LieModel (K ⧸ center K) .PSU m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSU m 2 n := hM.statedClassicalModel (by decide)
  by_cases hcase : ¬ Even n ∨ 8 ≤ m
  · refine uc22p20x_excl_three ?_
    rw [uc22p20w_pRank_psu hT hq hS Nat.prime_three (by norm_num)]
    by_cases hev : Even n
    · exact uc22p20v_four_le_rkLin_false_two (by rw [uc22p20v_eM_three, if_pos hev])
        (hcase.resolve_left (not_not.2 hev))
    · exact uc22p20v_four_le_rkLin_false_one Nat.prime_three
        (by rw [uc22p20v_eM_three, if_neg hev]) hm (fun _ => by norm_num)
  · obtain ⟨hev', hm8⟩ := not_or.1 hcase
    have hev : Even n := not_not.1 hev'
    obtain ⟨p, hp, hpd, hp3, hp5⟩ := uc22p20o_prime_add_one_ne_three_five (n := n)
      (by obtain ⟨k, hk⟩ := hev; omega)
    have hp2 := uc22p20v_ne_two_of_dvd_add_one (by omega) hp hpd
    refine uc22p20x_excl_borel hp hp2 ?_
      (hres.unitary K hq hodd m n (by omega) hn hev hM p hp hpd hp5)
    rw [uc22p20w_pRank_psu hT hq hS hp hp2]
    exact uc22p20v_four_le_rkLin_false_one hp (uc22p20v_eM_of_dvd hpd) hm (fun _ => hp5)

theorem uc22p20x_excl_u54 (hT : LieOddRankChev) (hN : uc22p20rNativeGriess) (hres : uc22p20vExclRes)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) (hZ : center K ≠ ⊥)
    (hM : LieModel (K ⧸ center K) .PSU 5 2 2) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSU 5 2 2 := hM.statedClassicalModel (by decide)
  have h5 := uc22p20v_five_dvd_center_psu hN hq hodd hZ hM
  have h4 : CFSG.Open.pRank 5 (⊤ : Subgroup K) = 4 := by
    rw [uc22p20w_pRank_psu hT hq hS Nat.prime_five (by norm_num)]
    exact uc22p20v_rkLin_five_false (uc22p20v_eM_of_dvd (n := 2) (p := 5) (by norm_num)) h5
  exact uc22p20x_excl_borel Nat.prime_five (by norm_num) h4.ge (hres.u54 K hq hodd hZ hM)

theorem uc22p20x_excl_psp (hT : LieOddRankChev) (hq : CFSG.Open.IsQuasisimple K) {m n : ℕ}
    (hm : 4 ≤ m) (hM : LieModel (K ⧸ center K) .PSp m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSp m 2 n := hM.statedClassicalModel (by decide)
  refine uc22p20x_excl_three ?_
  rw [uc22p20w_pRank_psp hT hq hS Nat.prime_three (by norm_num),
    uc22p20v_rkSp_of_eS (uc22p20v_eS_three n)]
  exact hm

theorem uc22p20x_excl_pomegaPlus (hT : LieOddRankChev) (hq : CFSG.Open.IsQuasisimple K) {m n : ℕ}
    (hM : LieModel (K ⧸ center K) .POmegaPlus m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) := by
  have hS : StatedClassicalModel (K ⧸ center K) .POmegaPlus m 2 n :=
    hM.statedClassicalModel (by decide)
  refine uc22p20x_excl_three ?_
  rw [uc22p20w_pRank_pomegaPlus hT hq hS Nat.prime_three (by norm_num)]
  exact uc22p20v_rkOmPlus_ge hS.1.2.2 (uc22p20v_eS_three n) (uc22p20v_eP_three_cases n)

theorem uc22p20x_excl_pomegaMinus (hT : LieOddRankChev) (hq : CFSG.Open.IsQuasisimple K) {m n : ℕ}
    (hm : 5 ≤ m) (hM : LieModel (K ⧸ center K) .POmegaMinus m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) := by
  have hS : StatedClassicalModel (K ⧸ center K) .POmegaMinus m 2 n :=
    hM.statedClassicalModel (by decide)
  refine uc22p20x_excl_three ?_
  rw [uc22p20w_pRank_pomegaMinus hT hq hS Nat.prime_three (by norm_num)]
  exact le_trans (by omega) (uc22p20v_rkOmMinus_ge (l := m) (uc22p20v_eS_three n))

end Excl

section ExclExc


variable {K : Type} [Group K] [Finite K]

theorem uc22p20x_excl_exc (hN : uc22p20rNativeGriess) (hq : CFSG.Open.IsQuasisimple K)
    (hodd : Odd (Nat.card (center K))) {t : StatedLieTag} {m n : ℕ}
    (ht : t = .F4 ∨ t = .E7 ∨ t = .E8) (hn : 1 ≤ n) (hM : LieModel (K ⧸ center K) t m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) := by
  have hZ : center K = ⊥ := by
    rcases ht with rfl | rfl | rfl
    · exact uc22p20v_center_f4 hN hq hodd hM
    · exact uc22p20v_center_e7 hN hq hodd hn hM
    · exact uc22p20v_center_e8 hN hq hodd hM
  refine uc22p20x_excl_three (uc22p20w_four_le_pRank_three_exc hZ ?_ hn hM)
  rcases ht with rfl | rfl | rfl <;> simp

theorem uc22p20x_excl_e (hres : uc22p20vExclRes) (hq : CFSG.Open.IsQuasisimple K)
    (hodd : Odd (Nat.card (center K))) {t : StatedLieTag} {m n : ℕ} (ht : t = .E6 ∨ t = .twistedE6)
    (hn : 2 < n) (hM : LieModel (K ⧸ center K) t m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2)) := by
  by_cases hZ : center K = ⊥
  · refine uc22p20x_excl_three (uc22p20w_four_le_pRank_three_exc hZ ?_ (by omega) hM)
    rcases ht with rfl | rfl <;> simp
  · obtain ⟨p, hp, hpd, hp3⟩ := uc22p20o_prime_sub_one_ne_three (n := n) (by omega)
    have hp2 := uc22p20v_ne_two_of_dvd_sub_one (by omega) hp hpd
    have hm0 : m = 0 := (uc22p20v_exc_model hM (by rcases ht with rfl | rfl <;> decide)).1
    subst hm0
    have hM' : LieModel (K ⧸ center K) .E6 0 2 n ∨ LieModel (K ⧸ center K) .twistedE6 0 2 n := by
      rcases ht with rfl | rfl
      · exact Or.inl hM
      · exact Or.inr hM
    have hB := hres.e K hq hodd hZ n hn hM' p hp hpd hp3
    exact ⟨p, hp, hp2, Or.inr ⟨uc22p20v_rankWit_of_borelWit hB,
      uc22p20v_borelWit_mono hp hB (by norm_num)⟩⟩

end ExclExc

section ExclMain


theorem uc22p20x_excl_of_res (hG : CFSG.Open.GriessAllModelsStatement) (hN : uc22p20rNativeGriess)
    (hres : uc22p20vExclRes) : uc22p20oExclWitness := by
  have hT := uc22p20x_lieOddRankChev hG
  intro K _ _ hq hodd t m n hfam hM
  rcases hfam with ⟨hn, hcases⟩ | ⟨rfl, rfl, rfl, hZ⟩
  · rcases hcases with ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | rfl | ⟨rfl, hm⟩ | rfl | rfl | rfl | rfl | rfl
    · exact uc22p20x_excl_psl hT hres hq hodd hm hn hM
    · exact uc22p20x_excl_psu hT hres hq hodd hm hn hM
    · exact uc22p20x_excl_psp hT hq hm hM
    · exact uc22p20x_excl_pomegaPlus hT hq hM
    · exact uc22p20x_excl_pomegaMinus hT hq hm hM
    · exact uc22p20x_excl_exc hN hq hodd (Or.inl rfl) (by omega) hM
    · exact uc22p20x_excl_e hres hq hodd (Or.inl rfl) hn hM
    · exact uc22p20x_excl_exc hN hq hodd (Or.inr (Or.inl rfl)) (by omega) hM
    · exact uc22p20x_excl_exc hN hq hodd (Or.inr (Or.inr rfl)) (by omega) hM
    · exact uc22p20x_excl_e hres hq hodd (Or.inr rfl) hn hM
  · exact uc22p20x_excl_u54 hT hN hres hq hodd hZ hM

end ExclMain

section Two

variable {K : Type} [Group K] [Finite K]

theorem uc22p20x_two_three (hZ : ¬ 3 ∣ Nat.card (center K))
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) :=
  ⟨3, Nat.prime_three, by norm_num, hZ, uc22p20r_rankWit_of_le_pRank Nat.prime_three h, Or.inl rfl⟩

theorem uc22p20x_not_dvd_of_bot {p : ℕ} (hp : p.Prime) (hZ : center K = ⊥) :
    ¬ p ∣ Nat.card (center K) := by
  rw [hZ, Subgroup.card_bot]
  exact hp.not_dvd_one

theorem uc22p20x_two_borel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (center K))
    (hB : uc22p20oBorelWit K p 2) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) :=
  ⟨p, hp, hp2, hZ, uc22p20v_rankWit_of_borelWit hB,
    Or.inr (uc22p20v_borelWit_mono hp hB (by norm_num))⟩

theorem uc22p20x_two_lin3 (hT : LieOddRankChev) (hN : uc22p20rNativeGriess) (hres : uc22p20vTwoRes)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {n : ℕ} (hn : 2 < n)
    (hM : LieModel (K ⧸ center K) .PSL 3 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSL 3 2 n := hM.statedClassicalModel (by decide)
  obtain ⟨p, hp, hpd, hp3⟩ := uc22p20o_prime_sub_one_ne_three (n := n) (by omega)
  have hp2 := uc22p20v_ne_two_of_dvd_sub_one (by omega) hp hpd
  have hZ := uc22p20v_center_dvd_three_psl hN hq hodd hM
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup K) = 2 := by
    rw [uc22p20w_pRank_psl hT hq hS le_rfl (by omega) hp hp2]
    exact uc22p20v_rkLin_three_true (uc22p20v_eP_of_dvd hpd)
  exact ⟨p, hp, hp2,
    fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hd.trans hZ)),
    uc22p20r_rankWit_of_le_pRank hp h2.ge, Or.inr (hres.lin3 K hq hodd n hn hM p hp hpd hp3)⟩

theorem uc22p20x_two_lin4 (hT : LieOddRankChev) (hN : uc22p20rNativeGriess)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {n : ℕ} (hn : 2 < n)
    (hM : LieModel (K ⧸ center K) .PSL 4 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSL 4 2 n := hM.statedClassicalModel (by decide)
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .PSL 4 n
    (by unfold uc22p20oNoOddMult; simp [hn]) hM
  refine uc22p20x_two_three (uc22p20x_not_dvd_of_bot Nat.prime_three hZ) ?_
  rw [uc22p20w_pRank_psl hT hq hS (by norm_num) (by omega) Nat.prime_three (by norm_num)]
  exact uc22p20v_two_le_rkLin_four_true (uc22p20v_eP_three_cases n)

theorem uc22p20x_two_unitary3 (hT : LieOddRankChev) (hN : uc22p20rNativeGriess)
    (hres : uc22p20vTwoRes) (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K)))
    {n : ℕ} (hn : 2 < n) (hn3 : n ≠ 3) (hM : LieModel (K ⧸ center K) .PSU 3 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSU 3 2 n := hM.statedClassicalModel (by decide)
  obtain ⟨p, hp, hpd, hp3, -⟩ := uc22p20o_prime_add_one_ne_three_five (n := n) (by omega)
  have hp2 := uc22p20v_ne_two_of_dvd_add_one (by omega) hp hpd
  have hZ := uc22p20v_center_dvd_three_psu hN hq hodd hM
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup K) = 2 := by
    rw [uc22p20w_pRank_psu hT hq hS hp hp2]
    exact uc22p20v_rkLin_three_false (uc22p20v_eM_of_dvd hpd)
  exact ⟨p, hp, hp2,
    fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hd.trans hZ)),
    uc22p20r_rankWit_of_le_pRank hp h2.ge, Or.inr (hres.unitary3 K hq hodd n hn hM p hp hpd hp3)⟩

theorem uc22p20x_two_unitary4 (hT : LieOddRankChev) (hN : uc22p20rNativeGriess)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {n : ℕ} (hn : 2 ≤ n)
    (hM : LieModel (K ⧸ center K) .PSU 4 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSU 4 2 n := hM.statedClassicalModel (by decide)
  have hNo : uc22p20oNoOddMult .PSU 4 n := by
    rcases (show 2 < n ∨ n = 2 by omega) with h | rfl
    · unfold uc22p20oNoOddMult; simp [h]
    · unfold uc22p20oNoOddMult; simp
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .PSU 4 n hNo hM
  refine uc22p20x_two_three (uc22p20x_not_dvd_of_bot Nat.prime_three hZ) ?_
  rw [uc22p20w_pRank_psu hT hq hS Nat.prime_three (by norm_num)]
  exact uc22p20v_two_le_rkLin_four_false (uc22p20v_eM_three_cases n)

theorem uc22p20x_two_u54 (hT : LieOddRankChev) (hN : uc22p20rNativeGriess)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K)))
    (hM : LieModel (K ⧸ center K) .PSU 5 2 2) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSU 5 2 2 := hM.statedClassicalModel (by decide)
  have hZ := uc22p20v_center_dvd_five_psu hN hq hodd hM
  refine uc22p20x_two_three (fun hd => ?_) ?_
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_five).1 (hd.trans hZ)
    omega
  · rw [uc22p20w_pRank_psu hT hq hS Nat.prime_three (by norm_num),
      uc22p20v_rkLin_false_two (by rw [uc22p20v_eM_three, if_pos (by decide)])]

theorem uc22p20x_two_psp (hT : LieOddRankChev) (hN : uc22p20rNativeGriess)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m n : ℕ} (hn : 2 < n)
    (hm : m = 2 ∨ m = 3) (hM : LieModel (K ⧸ center K) .PSp m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hS : StatedClassicalModel (K ⧸ center K) .PSp m 2 n := hM.statedClassicalModel (by decide)
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .PSp m n
    (by unfold uc22p20oNoOddMult; simp [hn, hm]) hM
  refine uc22p20x_two_three (uc22p20x_not_dvd_of_bot Nat.prime_three hZ) ?_
  rw [uc22p20w_pRank_psp hT hq hS Nat.prime_three (by norm_num),
    uc22p20v_rkSp_of_eS (uc22p20v_eS_three n)]
  omega

theorem uc22p20x_two_om8m (hT : LieOddRankChev) (hN : uc22p20rNativeGriess)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {n : ℕ} (hn : 2 ≤ n)
    (hM : LieModel (K ⧸ center K) .POmegaMinus 4 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hS : StatedClassicalModel (K ⧸ center K) .POmegaMinus 4 2 n :=
    hM.statedClassicalModel (by decide)
  have hNo : uc22p20oNoOddMult .POmegaMinus 4 n := by
    rcases (show 2 < n ∨ n = 2 by omega) with h | rfl
    · unfold uc22p20oNoOddMult; simp [h]
    · unfold uc22p20oNoOddMult; simp
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .POmegaMinus 4 n hNo hM
  refine uc22p20x_two_three (uc22p20x_not_dvd_of_bot Nat.prime_three hZ) ?_
  rw [uc22p20w_pRank_pomegaMinus hT hq hS Nat.prime_three (by norm_num)]
  exact le_trans (by omega) (uc22p20v_rkOmMinus_ge (l := 4) (uc22p20v_eS_three n))

theorem uc22p20x_two_d4 (hN : uc22p20rNativeGriess) (hres : uc22p20vTwoRes)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m n : ℕ} (hn : 2 ≤ n)
    (hM : LieModel (K ⧸ center K) .trialityD4 m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hNo : uc22p20oNoOddMult .trialityD4 m n := by
    rcases (show 2 < n ∨ n = 2 by omega) with h | rfl
    · unfold uc22p20oNoOddMult; simp [h]
    · unfold uc22p20oNoOddMult; simp
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .trialityD4 m n hNo hM
  have hm0 : m = 0 := (uc22p20v_exc_model hM (by decide)).1
  subst hm0
  obtain ⟨p, hp, hpd⟩ := uc22p20v_exists_prime_dvd_sub_one hn
  have hp2 := uc22p20v_ne_two_of_dvd_sub_one (by omega) hp hpd
  exact uc22p20x_two_borel hp hp2 (uc22p20x_not_dvd_of_bot hp hZ) (hres.d4 K hq hodd n hM p hp hpd)

theorem uc22p20x_two_d4two (hN : uc22p20rNativeGriess) (hres : uc22p20vTwoRes)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m : ℕ}
    (hM : LieModel (K ⧸ center K) .trialityD4 m 2 1) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .trialityD4 m 1
    (by unfold uc22p20oNoOddMult; simp) hM
  have hm0 : m = 0 := (uc22p20v_exc_model hM (by decide)).1
  subst hm0
  exact ⟨3, Nat.prime_three, by norm_num, uc22p20x_not_dvd_of_bot Nat.prime_three hZ,
    hres.d4two K hq hodd hM, Or.inl rfl⟩

theorem uc22p20x_two_f4 (hN : uc22p20rNativeGriess) (hres : uc22p20vTwoRes)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m n : ℕ} (hn : 2 < n)
    (hM : LieModel (K ⧸ center K) .twistedF4 m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .twistedF4 m n
    (by unfold uc22p20oNoOddMult; simp [hn]) hM
  have hm0 : m = 0 := (CFSG.Blueprint.LieModel.reeTitsModel hM (by decide)).1
  subst hm0
  obtain ⟨p, hp, hpd⟩ := uc22p20v_exists_prime_dvd_sub_one (by omega : 2 ≤ n)
  have hp2 := uc22p20v_ne_two_of_dvd_sub_one (by omega) hp hpd
  exact uc22p20x_two_borel hp hp2 (uc22p20x_not_dvd_of_bot hp hZ) (hres.f4 K hq hodd n hM p hp hpd)

end Two

section TwoG2


variable {K : Type} [Group K] [Finite K]

theorem uc22p20x_two_g2 (hT : LieOddRankChev) (hN : uc22p20rNativeGriess)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m n : ℕ} (hn : 2 < n)
    (hM : LieModel (K ⧸ center K) .G2 m 2 n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
      (p = 3 ∨ uc22p20oBorelWit K p 1) := by
  have hZ : center K = ⊥ := uc22p20r_center_of_native hN K hq hodd .G2 m n
    (by unfold uc22p20oNoOddMult; simp [hn]) hM
  have hE := (uc22p20v_exc_model hM (by decide)).2
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 2 := by
    rw [uc22p20w_pRank_g2 hT hq (by omega) hE Nat.prime_three (by norm_num)]
    exact uc22p20v_rkG2_of_eS (uc22p20v_eS_three n)
  exact uc22p20x_two_three (uc22p20x_not_dvd_of_bot Nat.prime_three hZ) h2.ge

end TwoG2

section TwoMain


theorem uc22p20x_two_of_res (hG : CFSG.Open.GriessAllModelsStatement) (hN : uc22p20rNativeGriess)
    (hres : uc22p20vTwoRes) : uc22p20oTwoWitness := by
  have hT := uc22p20x_lieOddRankChev hG
  intro K _ _ hq hodd t m n hfam hM hU3
  rcases hfam with ⟨hn, hcases⟩ | ⟨rfl, hcases⟩ | ⟨rfl, rfl⟩
  · rcases hcases with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | rfl | rfl | rfl | ⟨rfl, hm⟩ | ⟨rfl, rfl⟩
    · exact uc22p20x_two_lin3 hT hN hres hq hodd hn hM
    · exact uc22p20x_two_lin4 hT hN hq hodd hn hM
    · exact uc22p20x_two_unitary3 hT hN hres hq hodd hn (fun h => hU3 ⟨rfl, rfl, h⟩) hM
    · exact uc22p20x_two_unitary4 hT hN hq hodd (by omega) hM
    · exact uc22p20x_two_g2 hT hN hq hodd hn hM
    · exact uc22p20x_two_d4 hN hres hq hodd (by omega) hM
    · exact uc22p20x_two_f4 hN hres hq hodd hn hM
    · exact uc22p20x_two_psp hT hN hq hodd hn hm hM
    · exact uc22p20x_two_om8m hT hN hq hodd (by omega) hM
  · rcases hcases with ⟨rfl, rfl | rfl⟩ | rfl | ⟨rfl, rfl⟩
    · exact uc22p20x_two_unitary4 hT hN hq hodd le_rfl hM
    · exact uc22p20x_two_u54 hT hN hq hodd hM
    · exact uc22p20x_two_d4 hN hres hq hodd le_rfl hM
    · exact uc22p20x_two_om8m hT hN hq hodd le_rfl hM
  · exact uc22p20x_two_d4two hN hres hq hodd hM

end TwoMain

section Certificates


theorem uc22p20x_excl (hres : uc22p20vExclRes) : uc22p20oExclWitness :=
  uc22p20x_excl_of_res CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    uc22p20r_nativeGriess hres

theorem uc22p20x_two (hres : uc22p20vTwoRes) : uc22p20oTwoWitness :=
  uc22p20x_two_of_res CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    uc22p20r_nativeGriess hres

theorem uc22p20x_global22f_of (hexcl : uc22p20vExclRes) (htwo : uc22p20vTwoRes) : Global22f :=
  uc22p20r_global22f_of (uc22p20x_excl hexcl) (uc22p20x_two htwo)

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.UC22
