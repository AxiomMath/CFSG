module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Strong
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl1
import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedU3 (L : Subgroup G) : Prop :=
  ∃ n q : ℕ, LieModel (BarInf L) .PSU 3 2 n ∧ q.Prime ∧ 3 < q ∧ q ∣ 2 ^ n + 1

private theorem uc22s213_three_thousand_lt_card_u3 {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hX : LieModel X .PSU 3 2 n) : 3600 < Nat.card X := by
  have hc := CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX)
  have hQ : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hd : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have h64 : 64 ≤ (2 ^ n) ^ 3 :=
    (show 64 = 4 ^ 3 by norm_num) ▸ Nat.pow_le_pow_left hQ 3
  have h16 : 16 ≤ (2 ^ n) ^ 2 :=
    (show 16 = 4 ^ 2 by norm_num) ▸ Nat.pow_le_pow_left hQ 2
  have hN : 64 * (15 * 65) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) :=
    Nat.mul_le_mul h64 (Nat.mul_le_mul (by omega) (by omega))
  by_contra hle
  push Not at hle
  have := Nat.mul_le_mul hle hd
  omega

theorem uc22s213_not_centralizesBar_of_u3 (hgr : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable) (hB : BadNoStrongThree)
    (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S)) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hU3 : S21_3ClosedU3 L) {a : G} (ha : a ∈ c.B)
    (hpr : (orderOf a).Prime) : ¬ CentralizesBar a L := by
  obtain ⟨n, q, hX, hq, hq3, hqn⟩ := hU3
  have hq2 : q ≠ 2 := by omega
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨e⟩ := uc22p21k_barInf_equiv hL.2.2
  have hSU : IsSU3 (Bar2 L) n := ⟨hL.2.2, CFSG.Blueprint.LieModel.of_mulEquiv e hX⟩
  have hZ : ¬ q ∣ Nat.card (center (Bar2 L)) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans (UCK.u3Center_of_griess hgr (Bar2 L) n hSU))
    omega
  obtain ⟨Sb⟩ : Nonempty (Sylow q (Bar2 L)) := inferInstance
  obtain ⟨Eb, -, hEbel, hEbcard, -⟩ := UCK.u3SylOmega_of_griess hgr (Bar2 L) n hSU q hq hq3 hqn
    Sb Sb.isPGroup' Sb.not_dvd_index
  have hrL : 2 ≤ CFSG.Open.pRank q L := by
    rw [← pRank_bar2_eq_of_odd (Y := L) hq hq2]
    exact CFSG.SectionRank.le_pRank hq.one_lt le_top hEbel hEbcard
  have hrB : q ∣ Nat.card (BarInf L) := by
    have h1 : 1 ≤ CFSG.Open.pRank q (⊤ : Subgroup (BarInf L)) := by
      rw [uc22s213_pRank_barInf_of_prime hL.2.2 hq hq2 hZ]
      omega
    have h2 := CFSG.GroupTheory.dvd_card_of_one_le_pRank hq h1
    rwa [Subgroup.card_top] at h2
  have hn2 : 2 ≤ n := by
    by_contra hn
    interval_cases n <;> norm_num at hqn <;> have := Nat.le_of_dvd (by norm_num) hqn <;> omega
  have hq5 : 5 ≤ q := by
    by_contra h
    exact absurd ((show q = 4 by omega) ▸ hq) (by norm_num)
  exact uc22s213_not_centralizesBar_of_strong hS hU S hσ hPart hSE hSS hB Ch hH c hL hq hq5
    (h846 L hL n hSU q hq hq3 hqn) hrL hrB
    (uc22s213_three_thousand_lt_card_u3 hn2 hX) ha hpr

end CFSG.LocalAnalysis.UniquenessCase.UC22
