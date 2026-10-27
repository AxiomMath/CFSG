module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianFamilies
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L3CartanThreeHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)

theorem k_L34OddCover_holds :
    K_L34OddCover := by
  intro K _ _ _ hL hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O := CFSG.Open.pCoreOf 2 (Subgroup.center K)
  have hOcenter : O ≤ Subgroup.center K := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hOnormal : O.Normal := Subgroup.normal_of_le_center hOcenter
  have hOeq : O = CFSG.pCore 2 K := by
    refine le_antisymm ?_ ?_
    · simp only [CFSG.pCore]
      exact le_sSup ⟨hOnormal,
        (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.center K))).map
          (Subgroup.center K).subtype⟩
    · change CFSG.pCore 2 K ≤ CFSG.Open.pCoreOf 2 (Subgroup.center K)
      have hp : CFSG.pCore 2 K ≤ Subgroup.center K :=
        GL83.I243.Cover.pCore_le_center (p := 2) hq
      refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hp ?_
        (CFSG.pCore_isPGroup (p := 2) (G := K))
      intro x hx y hy
      have hc : x * y * x⁻¹ = y := by
        rw [show x * y = y * x from (Subgroup.mem_center_iff.mp hx y).symm]
        group
      simpa [hc] using hy
  have hodd : Odd (Nat.card (Subgroup.center (K ⧸ O))) := by
    let e : K ⧸ O ≃* K ⧸ CFSG.pCore 2 K :=
      QuotientGroup.quotientMulEquivOfEq hOeq
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 K
  have hQ : CFSG.Open.IsQuasisimple (K ⧸ O) :=
    CFSG.ComponentClassification.Quasisimple.central_quotient hq O hOcenter
  have : Group.IsPerfect K := ⟨hq.1⟩
  have hcenter : Subgroup.center (K ⧸ O) =
      (Subgroup.center K).map (QuotientGroup.mk' O) :=
    (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
      (by rw [QuotientGroup.ker_mk']; exact hOcenter)).symm
  let eZ : (K ⧸ O) ⧸ Subgroup.center (K ⧸ O) ≃* K ⧸ Subgroup.center K :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientQuotientEquivQuotient O (Subgroup.center K) hOcenter)
  have hL' : LieModel ((K ⧸ O) ⧸ Subgroup.center (K ⧸ O)) .PSL 3 2 2 :=
    hL.of_mulEquiv eZ.symm
  have hadm : StatedLieAdmissible .PSL 3 2 2 := by
    simp only [StatedLieAdmissible]
    exact ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  obtain ⟨F, hField, hFin, hF2, α, hαsurj, hαker⟩ :=
    exists_sl3_cover (K := K ⧸ O) (f := 2) hadm (by norm_num) hL' hQ hodd
  have hF4 : Nat.card F = 4 := by
    rw [hF2]
    norm_num
  have hαodd : Odd (Nat.card α.ker) := by
    have hdvd : Nat.card α.ker ∣ 3 := by
      refine (Subgroup.card_dvd_of_le hαker).trans ?_
      have h := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd
        (n := 3) (by norm_num) F
      rw [hF4] at h
      norm_num at h
      exact h
    exact Odd.of_dvd_nat (by norm_num : Odd 3) hdvd
  exact ⟨F, hField, hFin,
    @CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_charP_two F hField hFin 2 hF2,
    α, hF4, hαsurj, hαker, hαodd⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
