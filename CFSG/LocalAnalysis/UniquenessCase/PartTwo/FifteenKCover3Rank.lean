module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltMult
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3Omega
import CFSG.Open.StatedZModTwo
public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s15k_cov_card_table (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  simp only [generic, exceptional, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _), Nat.card_zmod]

private theorem s15k_cov_center_of_table (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type}
    [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (hodd : Odd (Nat.card (center X))) {t : StatedLieTag} {n : ℕ}
    (hm : CFSG.Models.LieModel (X ⧸ center X) t n 2 1)
    (hord : ((genericOrders t n 2 1).1 * (genericOrders t n 2 1).2) *
      ((exceptionalOrders t n 2 1).1 * (exceptionalOrders t n 2 1).2) ∣ 4) : center X = ⊥ := by
  obtain ⟨-, ⟨e⟩⟩ := hGA _ t n 2 1 hm
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (X ⧸ center X)) =
      ((genericOrders t n 2 1).1 * (genericOrders t n 2 1).2) *
        ((exceptionalOrders t n 2 1).1 * (exceptionalOrders t n 2 1).2) := by
    rw [Nat.card_congr e.toEquiv, s15k_cov_card_table]
  have hne : ((genericOrders t n 2 1).1 * (genericOrders t n 2 1).2) *
      ((exceptionalOrders t n 2 1).1 * (exceptionalOrders t n 2 1).2) ≠ 0 := fun h0 => by
    rw [h0] at hord
    exact absurd (Nat.eq_zero_of_zero_dvd hord) (by norm_num)
  have : Finite (CFSG.Open.griessHopfMultiplier (X ⧸ center X)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne)
  have h1 := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf
    (s15_Three_qs_of_open hq) (MulEquiv.refl (X ⧸ center X))
  rw [hcard] at h1
  have h2 : Nat.card (center X) ∣ 4 := h1.trans hord
  have h3 : Nat.card (center X) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) h2
    obtain ⟨k, hk⟩ := hodd
    generalize Nat.card (center X) = m at h2 hle hk ⊢
    interval_cases m <;> omega
  exact Subgroup.card_eq_one.mp h3

private theorem s15k_cov_table_psl (n : ℕ) :
    ((genericOrders .PSL n 2 1).1 * (genericOrders .PSL n 2 1).2) *
      ((exceptionalOrders .PSL n 2 1).1 * (exceptionalOrders .PSL n 2 1).2) ∣ 4 := by
  rcases n with _ | _ | _ | _ | _ | n <;> simp [genericOrders, exceptionalOrders]

private theorem s15k_cov_table_psp (n : ℕ) :
    ((genericOrders .PSp n 2 1).1 * (genericOrders .PSp n 2 1).2) *
      ((exceptionalOrders .PSp n 2 1).1 * (exceptionalOrders .PSp n 2 1).2) ∣ 4 := by
  rcases n with _ | _ | _ | _ | n <;> simp [genericOrders, exceptionalOrders]

private theorem s15k_cov_table_pomp (n : ℕ) :
    ((genericOrders .POmegaPlus n 2 1).1 * (genericOrders .POmegaPlus n 2 1).2) *
      ((exceptionalOrders .POmegaPlus n 2 1).1 * (exceptionalOrders .POmegaPlus n 2 1).2) ∣ 4 := by
  rcases n with _ | _ | _ | _ | _ | n <;> simp [genericOrders, exceptionalOrders]

private theorem s15k_cov_table_pomm (n : ℕ) :
    ((genericOrders .POmegaMinus n 2 1).1 * (genericOrders .POmegaMinus n 2 1).2) *
      ((exceptionalOrders .POmegaMinus n 2 1).1 *
        (exceptionalOrders .POmegaMinus n 2 1).2) ∣ 4 := by
  simp only [genericOrders, exceptionalOrders]
  simpa using Nat.gcd_dvd_left 4 (2 ^ n + 1)

private theorem s15k_cov_table_psu_four :
    ((genericOrders .PSU 4 2 1).1 * (genericOrders .PSU 4 2 1).2) *
      ((exceptionalOrders .PSU 4 2 1).1 * (exceptionalOrders .PSU 4 2 1).2) ∣ 4 := by
  simp [genericOrders, exceptionalOrders]

private theorem s15k_cov_model_psl {Y Z : Type} [Group Y] [Group Z] (e : Z ≃* Y) {n : ℕ}
    (hn : 3 ≤ n) (h : IsLn Y n 1) : CFSG.Models.LieModel Z .PSL n 2 1 := by
  obtain ⟨hadm, K, hF, hfin, hK, ⟨eK⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) h
  exact ⟨hadm, Or.inl ⟨hadm, K, hF, hfin, hK, ⟨e.trans eK⟩⟩⟩

private theorem s15k_cov_model_psp {Y Z : Type} [Group Y] [Group Z] (e : Z ≃* Y) {n : ℕ}
    (hn : 6 ≤ n) (h : IsSpn Y n 1) : CFSG.Models.LieModel Z .PSp (n / 2) 2 1 := by
  obtain ⟨-, K, hF, hfin, hK, ⟨eK⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hbot : (StatedScalars (Fin (n / 2) ⊕ Fin (n / 2)) K).subgroupOf (StatedSp (n / 2) K) =
      ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK2, Subgroup.bot_subgroupOf]
  have hadm : StatedLieAdmissible .PSp (n / 2) 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, fun h => absurd (congrArg Prod.fst h) (by omega)⟩
  exact ⟨hadm, Or.inl ⟨hadm, K, hF, hfin, hK,
    ⟨(e.trans eK).trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans
      QuotientGroup.quotientBot).symm⟩⟩⟩

private theorem s15k_cov_model_pomp {Y Z : Type} [Group Y] [Group Z] (e : Z ≃* Y) {n : ℕ}
    (hn : 8 ≤ n) (h : IsOmegaPlus Y n 1) : CFSG.Models.LieModel Z .POmegaPlus (n / 2) 2 1 := by
  obtain ⟨-, K, hF, hfin, hK, ⟨eK⟩⟩ := h
  have hadm : StatedLieAdmissible .POmegaPlus (n / 2) 2 1 := ⟨Nat.prime_two, le_rfl, by omega⟩
  exact ⟨hadm, Or.inl ⟨hadm, K, hF, hfin, hK, ⟨e.trans eK⟩⟩⟩

private theorem s15k_cov_model_pomm {Y Z : Type} [Group Y] [Group Z] (e : Z ≃* Y) {n : ℕ}
    (hn : 8 ≤ n) (h : IsOmegaMinus Y n 1) : CFSG.Models.LieModel Z .POmegaMinus (n / 2) 2 1 := by
  obtain ⟨-, K, hF, hfin, b, c, hK, hirr, ⟨eK⟩⟩ := h
  have hadm : StatedLieAdmissible .POmegaMinus (n / 2) 2 1 := ⟨Nat.prime_two, le_rfl, by omega⟩
  exact ⟨hadm, Or.inl ⟨hadm, K, hF, hfin, hK, b, c, hirr, ⟨e.trans eK⟩⟩⟩

private theorem s15k_cov_model_psu {Y Z : Type} [Group Y] [Group Z] (e : Z ≃* Y)
    (h : IsOmegaMinus Y 6 1) : CFSG.Models.LieModel Z .PSU 4 2 1 := by
  obtain ⟨F, hF, hU, ⟨eU⟩⟩ := s15k_om6_model h
  haveI : Finite F := hU.finite
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by rw [hU.card]; norm_num
  have hbot := CFSG.RankThree.PartOne.KFU.scalars_subgroupOf_eq_bot (K := F) (f := 1) (n := 4)
    hK (by norm_num) (by norm_num)
  have hadm : StatedLieAdmissible .PSU 4 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, fun h => absurd (congrArg Prod.fst h) (by norm_num)⟩
  exact ⟨hadm, Or.inl ⟨hadm, F, hF, ‹Finite F›, hK,
    ⟨(e.trans eU).trans (CFSG.RankThree.PartOne.KFU.projEquivOfBot hbot).symm⟩⟩⟩

private theorem s15k_cov_center_alt {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (center X))) {n : ℕ} (hn : 8 ≤ n)
    (e : X ⧸ center X ≃* alternatingGroup (Fin n)) : center X = ⊥ := by
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.card_center_dvd_of_alt
    (s15_Three_qs_of_open hq) (by omega : 5 ≤ n) e
  rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup hn] at hd
  have h1 : Nat.card (center X) = 1 := by
    have hle : Nat.card (center X) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    obtain ⟨k, hk⟩ := hodd
    omega
  exact Subgroup.card_eq_one.mp h1

private theorem s15k_cov_rank_alt_small {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : n ≤ 8)
    (h : UC22.IsAlt Y n) : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 := by
  obtain ⟨e⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact CFSG.SectionRank.pRank_alternating_le_two hn Nat.prime_three (by norm_num)

theorem rCover3Rank153_holds (hGA : CFSG.Open.GriessAllModelsStatement) : RCover3Rank153 := by
  intro X Y _ _ _ _ hq hodd ⟨e⟩ hshape hrank
  have hc : center X = ⊥ := by
    rcases hshape with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩
    · exact s15k_cov_center_of_table hGA hq hodd (s15k_cov_model_psl e hn h)
        (s15k_cov_table_psl n)
    · exact s15k_cov_center_of_table hGA hq hodd (s15k_cov_model_psp e hn h)
        (s15k_cov_table_psp (n / 2))
    · rcases Nat.lt_or_ge n 8 with h8 | h8
      · obtain ⟨k, hk⟩ := h.1
        obtain rfl : n = 6 := by omega
        obtain ⟨eA⟩ := s15k_omp6_isAlt8 h
        exact s15k_cov_center_alt hq hodd (le_refl 8) (e.trans eA)
      · exact s15k_cov_center_of_table hGA hq hodd (s15k_cov_model_pomp e h8 h)
          (s15k_cov_table_pomp (n / 2))
    · rcases Nat.lt_or_ge n 8 with h8 | h8
      · obtain ⟨k, hk⟩ := h.1
        obtain rfl : n = 6 := by omega
        exact s15k_cov_center_of_table hGA hq hodd (s15k_cov_model_psu e h)
          s15k_cov_table_psu_four
      · exact s15k_cov_center_of_table hGA hq hodd (s15k_cov_model_pomm e h8 h)
          (s15k_cov_table_pomm (n / 2))
    · rcases Nat.lt_or_ge n 8 with h8 | h8
      · exact absurd hrank (not_lt.mpr (s15k_cov_rank_alt_small (by omega) h))
      · obtain ⟨eA⟩ := h
        exact s15k_cov_center_alt hq hodd h8 (e.trans eA)
  let eX : X ≃* Y :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)).trans e
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) eX]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
