module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Lie
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CensusRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.SURank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem k_GF2_threeRank_of_native
    (hN : UC22.uc22p20rNativeGriess) :
    ∀ (K : Type) [Group K] [Finite K]
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m 2 1 →
      CFSG.Open.IsQuasisimple K → LieModel (K ⧸ Subgroup.center K) t m 2 1 →
      Odd (Nat.card (Subgroup.center K)) →
      CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 →
        (t = .PSL ∧ (m = 3 ∨ m = 4 ∨ m = 5)) ∨ t = .trialityD4 ∨ t = .Tits := by
  intro K _ _ t m hadm hq hM hodd h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3Q : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 3 :=
    CFSG.SectionRank.pRank_quotient_le_three (by norm_num) h3 _ le_rfl
  have hZ1 : CFSG.Blueprint.Multiplier.genericOrders t m 2 1 = (1, 1) →
      CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 2 := fun hg => by
    rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) (by
      rw [UC22.uc22p20v_center_eq_bot hN hq hodd hM hg, Subgroup.card_bot]
      norm_num)]
    exact h3
  cases t with
  | PSL =>
    obtain ⟨-, -, hm2, h22, -⟩ := hadm
    have hm3 : 3 ≤ m := by
      by_contra hlt
      obtain rfl : m = 2 := by omega
      exact h22 rfl
    rcases (show m = 3 ∨ m = 4 ∨ m = 5 ∨ 6 ≤ m by omega) with rfl | rfl | rfl | hm6
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩
    · exfalso
      obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := LieModel.statedClassicalModel_of_ne_zero (by omega) hM
      have : CharP K' 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
      have h1 := CFSG.SectionRank.ClassicalEven.psl_three_le_pRank_three (K := K') hm6
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h1
      have h2 := hZ1 (by
        change (Nat.gcd m (2 ^ 1 - 1), 1) = (1, 1)
        rw [show 2 ^ 1 - 1 = 1 from rfl, Nat.gcd_one_right])
      omega
  | PSU =>
    exfalso
    obtain ⟨-, -, hm3, h32⟩ := hadm
    have hm4 : 4 ≤ m := by
      by_contra hlt
      obtain rfl : m = 3 := by omega
      exact h32 rfl
    obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := LieModel.statedClassicalModel_of_ne_zero (by omega) hM
    have hK4 : Nat.card K' = 4 := by rw [hK']; norm_num
    rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | hm5
    · have h1 := CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.three_le_pRank_psu_two
        (K := K') hK4 le_rfl
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h1
      have h2 := hZ1 (by
        change (Nat.gcd 4 (2 ^ 1 + 1), 1) = (1, 1)
        rfl)
      omega
    · have hker : (QuotientGroup.mk' ((StatedScalars (Fin m) K').subgroupOf
          (StatedSU m (2 ^ 1) K'))).ker ≤ Subgroup.center (StatedSU m (2 ^ 1) K') := by
        rw [QuotientGroup.ker_mk']
        intro x hx
        rw [Subgroup.mem_subgroupOf, StatedScalars,
          ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext ((Subgroup.mem_center_iff.mp hx) (g : GL (Fin m) K'))
      have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.four_le_pRank_of_statedSU_hom
        hK4 hm5 _ hker
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h1
      omega
  | PSp =>
    exfalso
    obtain ⟨-, -, hm2, h22⟩ := hadm
    have hm3 : 3 ≤ m := by
      by_contra hlt
      obtain rfl : m = 2 := by omega
      exact h22 rfl
    obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := LieModel.statedClassicalModel_of_ne_zero (by omega) hM
    have : CharP K' 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
    have h1 := CFSG.SectionRank.ClassicalEven.psp_three_le_pRank_three (K := K') hm3
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h1
    have h2 := hZ1 (by
      change (Nat.gcd 2 (2 ^ 1 - 1), 1) = (1, 1)
      rfl)
    omega
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus =>
    exfalso
    obtain ⟨-, -, hm4⟩ := hadm
    obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := LieModel.statedClassicalModel_of_ne_zero (by omega) hM
    have : CharP K' 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
    have h1 := CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three (K := K') hm4
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h1
    have h2 := hZ1 (by
      change (if Even (2 ^ 1) then ((1 : ℕ), (1 : ℕ)) else
        if Even m then (2, 2) else (Nat.gcd 4 ((2 ^ 1) ^ m - 1), 1)) = (1, 1)
      rw [if_pos (by decide)])
    omega
  | POmegaMinus =>
    exfalso
    obtain ⟨-, -, hm4⟩ := hadm
    obtain ⟨-, K', _, _, hK', b, c, -, ⟨e⟩⟩ :=
      LieModel.statedClassicalModel_of_ne_zero (by omega) hM
    have : CharP K' 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
    have h1 := CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three (K := K') hm4 b c
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h1
    have h2 := hZ1 (by
      change (Nat.gcd 4 ((2 ^ 1) ^ m + 1), 1) = (1, 1)
      have hodd' : Odd ((2 ^ 1) ^ m + 1) :=
        (Nat.even_pow.mpr ⟨by decide, by omega⟩).add_one
      have hc : Nat.Coprime (2 ^ 2) ((2 ^ 1) ^ m + 1) :=
        Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd')
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, hc.gcd_eq_one])
    omega
  | G2 => exact absurd hadm.2.2.2 (by norm_num)
  | F4 =>
    exfalso
    obtain ⟨-, ⟨⟨-, -, -⟩, hm⟩⟩ := UC22.uc22p20v_exc_model hM (by decide)
    have h1 := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (by simp) hm
    omega
  | E6 =>
    exfalso
    obtain ⟨-, ⟨⟨-, -, -⟩, hm⟩⟩ := UC22.uc22p20v_exc_model hM (by decide)
    have h1 := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (by simp) hm
    omega
  | E7 =>
    exfalso
    obtain ⟨-, ⟨⟨-, -, -⟩, hm⟩⟩ := UC22.uc22p20v_exc_model hM (by decide)
    have h1 := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (by simp) hm
    omega
  | E8 =>
    exfalso
    obtain ⟨-, ⟨⟨-, -, -⟩, hm⟩⟩ := UC22.uc22p20v_exc_model hM (by decide)
    have h1 := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (by simp) hm
    omega
  | twistedE6 =>
    exfalso
    obtain ⟨-, ⟨⟨-, hf, -⟩, hm⟩⟩ := UC22.uc22p20v_exc_model hM (by decide)
    have h1 := CFSG.SectionRank.four_le_pRank_three_of_twistedE6Model_two hf hm
    omega
  | trialityD4 => exact Or.inr (Or.inl rfl)
  | twistedB2 => exact absurd hadm.2.2.2.2.2 (by norm_num)
  | twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  | twistedF4 => exact absurd hadm.2.2.2.2.2 (by norm_num)
  | Tits => exact Or.inr (Or.inr rfl)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
