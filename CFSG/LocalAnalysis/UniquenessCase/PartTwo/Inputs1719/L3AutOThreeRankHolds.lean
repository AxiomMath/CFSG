module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutThreeRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySevenE
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Matrix Subgroup CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PerfectCover
open scoped MatrixGroups

theorem k_L3AutOThreeRank_holds :
    K_L3AutOThreeRank := by
  intro K _ _ _ f hq hL3 h3dvd hodd
  classical
  have hperf : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  have hmodel : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL 3 2 f := hL3
  obtain ⟨hadm, F, _, _, hcardF, ⟨eF⟩⟩ :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  have hf1 : 1 ≤ f := hadm.2.1
  have card_center_dvd_hopf : ∀ {X : Type} [Group X],
      ((K ⧸ Subgroup.center K) ≃* X) →
        Nat.card (Subgroup.center K) ∣ Nat.card (hopfMultiplier X) := by
    intro X _ e
    have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective
      (CFSG.RankThree.PerfectCover.centralQuotientMap e)
      (CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e)
      (CFSG.RankThree.PerfectCover.centralQuotientMap_ker e).le
    have h := Subgroup.card_dvd_of_surjective hsurj
    rwa [CFSG.RankThree.PerfectCover.centralQuotientMap_ker e] at h
  constructor
  ·
    by_cases h4 : Nat.card F = 4
    ·
      have hf2 : f = 2 := by
        have h2 : 2 ^ f = 2 ^ 2 := by
          rw [← hcardF]
          simpa using h4
        exact Nat.pow_right_injective (show 2 ≤ 2 by norm_num) h2
      subst hf2
      obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four
        (K ⧸ Subgroup.center K) hmodel
      have hcardM : Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)) = 48 := by
        rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
          Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd]
        simp [Nat.card_prod, Nat.card_zmod]
      have hdvd : Nat.card (Subgroup.center K) ∣
          Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)) :=
        card_center_dvd_hopf (MulEquiv.refl _)
      rw [hcardM] at hdvd
      have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) 16 := by
        simpa using hodd.coprime_two_right.pow_right 4
      have h48 : Nat.card (Subgroup.center K) ∣ 16 * 3 := by simpa using hdvd
      exact hcop.dvd_mul_left.mp h48
    ·
      have h2f : 2 ≤ f := by
        rcases (show f = 0 ∨ f = 1 ∨ 2 ≤ f by omega) with rfl | rfl | h
        · omega
        · norm_num at h3dvd
        · exact h
      have h4le : 4 ≤ Nat.card F := by
        rw [hcardF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2f
      haveI : Fintype F := Fintype.ofFinite F
      have h5 : 5 ≤ Fintype.card F := by
        rw [Fintype.card_eq_nat_card]
        omega
      obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier
        (k := F) (n := 3) (by norm_num) h5
      have hcardM : Nat.card (hopfMultiplier (PSL(3, F))) = 3 := by
        rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
          Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
        rw [Fintype.card_eq_nat_card, hcardF]
        exact Nat.gcd_eq_left h3dvd
      have eP : (K ⧸ Subgroup.center K) ≃* PSL(3, F) :=
        eF.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
      have hdvd : Nat.card (Subgroup.center K) ∣ Nat.card (hopfMultiplier (PSL(3, F))) :=
        card_center_dvd_hopf eP
      rw [hcardM] at hdvd
      exact hdvd
  ·
    intro H hHres
    have eP : (K ⧸ Subgroup.center K) ≃* projectiveSL 3 F :=
      (eF.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
        (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 F)).symm
    let φ : MulAut K →* MulAut (projectiveSL 3 F) :=
      (MulAut.congr eP).toMonoidHom.comp
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)
    have hφinj : Function.Injective φ :=
      (MulAut.congr eP).injective.comp
        (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.centerQuotientHom_injective_of_commutator
          (L := K) hq.1)
    have hmapres : CFSG.GH74.GLS.oResidual 3 ↥(H.map φ) = ⊤ := by
      have hmap := CFSG.GH74.GLS.Balance.BenderExt.map_oResidual (A := ↥H) (B := ↥(H.map φ))
        Nat.prime_three (φ.subgroupMap H) (φ.subgroupMap_surjective H)
      rw [hHres, Subgroup.map_top_of_surjective _ (φ.subgroupMap_surjective H)] at hmap
      exact hmap.symm
    have hpK : 3 ∣ Nat.card Fˣ := by
      rw [Nat.card_units, hcardF]
      exact h3dvd
    refine (CFSG.SectionRank.pRank_le_map (by norm_num) φ hφinj H).trans ?_
    exact pRank_le_of_oResidual_eq_top (K := F) (n := 3) (by norm_num) Nat.prime_three
      (by norm_num) hpK hmapres

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
