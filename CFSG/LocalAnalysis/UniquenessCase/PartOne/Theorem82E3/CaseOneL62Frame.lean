module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsL62
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneOuter
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneYLemma
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOnePElementCentral
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieHolds
import CFSG.GH74.Orders.LieType
import CFSG.GroupTheory.PRankBound
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneAbar
import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K6a K6b IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem Ctx82E3.card_lbar_of_l62 (c : Ctx82E3 D) (hlie : IsLie811 c.Lbar .l6 2 1)
    (hZ : Subgroup.center c.Lbar = ⊥) : Nat.card c.Lbar = 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 := by
  obtain ⟨-, -, hfam⟩ := hlie
  obtain ⟨-, hcase⟩ := hfam
  rcases hcase with ⟨-, hm⟩ | ⟨hmod, -⟩
  · have hq : Nat.card (c.Lbar ⧸ Subgroup.center c.Lbar) = ordA 5 (2 ^ 1) :=
      CFSG.GH74.card_of_lieModel_PSL (by norm_num) hm
    have hcard : Nat.card c.Lbar = Nat.card (c.Lbar ⧸ Subgroup.center c.Lbar) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center c.Lbar), hZ,
        Subgroup.card_bot, mul_one]
    rw [hcard, hq]
    have h : ordA 5 (2 ^ 1) = 2 ^ 15 * 615195 := by decide
    rw [h]
    norm_num
  · norm_num at hmod

theorem Ctx82E3.nonempty_case811Sylow_of_l62 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK6a : K6a) (hK6b : K6b)
    (hlie : IsLie811 c.Lbar .l6 2 1) (hZ : Subgroup.center c.Lbar = ⊥) :
    Nonempty (Case811Sylow c) := by
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  have hPL : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M → P ≤ c.L := by
    intro P hP
    refine c.le_L_of_isSylowOf hZ3 ?_ hP
    intro R hR hRsyl hRnot
    have h4 := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k2Lie_holds c.Lbar .l6 2 1
      hlie ((CFSG.SectionRank.pRank_coe_eq_openPRank (p := 3)
        (H := (⊤ : Subgroup c.Lbar))).trans c.pRank_three_lbar) R hR hRsyl hRnot
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h4
  exact c.exists_case811Sylow_of_K6 hK6a hK6b hlie hPL

private theorem factorization_card_L_of_l62 (c : Ctx82E3 D) (hlie : IsLie811 c.Lbar .l6 2 1)
    (hZ : Subgroup.center c.Lbar = ⊥) :
    (Nat.card ↥c.L).factorization 3 = 4 := by
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  have hN3 : ¬ 3 ∣ Nat.card O :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hfacLbar : (Nat.card c.Lbar).factorization 3 = 4 := by
    rw [Ctx82E3.card_lbar_of_l62 c hlie hZ]
    have h : 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 = 3 ^ 4 * (2 ^ 15 * 5 * 7 ^ 2 * 31) := by
      ring
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hcardL : Nat.card ↥c.L = Nat.card c.Lbar * Nat.card O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  rw [hcardL, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hN3, add_zero, hfacLbar]

theorem Case811Sylow.card_P_of_l62 {c : Ctx82E3 D} (h : Case811Sylow c)
    (hlie : IsLie811 c.Lbar .l6 2 1) (hZ : Subgroup.center c.Lbar = ⊥) : Nat.card h.P = 81 := by
  have hPLsyl : CFSG.ABGLocalTools.IsSylowOf 3 h.P c.L :=
    h.sylow.of_le h.P_le_L c.hyp81.1
  rw [hPLsyl.card_eq, factorization_card_L_of_l62 c hlie hZ]
  norm_num

theorem Case811Sylow.exists_seven_of_l62 {c : Ctx82E3 D} (h : Case811Sylow c)
    (hCA : K7L6TwoCentA) (hlie : IsLie811 c.Lbar .l6 2 1) (hZ : Subgroup.center c.Lbar = ⊥)
    (h7 : 7 ∈ D.sig) :
    ∃ y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G), orderOf y = 7 ∧ y ∉ c.L := by
  have hL2 : CFSG.Open.pRank 7 c.L ≤ 2 := by
    rw [← Ctx82E3.pRank_lbar c (p := 7) (by norm_num)]
    refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (p := 7) (k := 2) (by norm_num) ?_
    rw [Subgroup.card_top, Ctx82E3.card_lbar_of_l62 c hlie hZ]
    norm_num
  have hnot : ¬ 7 ∣ Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
    rw [hCA c.Lbar hlie h.Abar h.isElemAbelian_Abar h.card_Abar]
    norm_num
  exact h.exists_mem_centralizer_A_not_mem_L h7
    (h.mem_centralizer_of_isPGroup_of_prime (p := 7) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) hL2 hnot

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
