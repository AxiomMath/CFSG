module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixParaTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixParaThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc2_14_6_of_inputs
    {D : Data G} (hx : DataExt D) (hσ3 : SigmaThree D)
    (h66 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_6 D) (h846 : F08.R846 D)
    (h869 : F08.R869 D) (h128 : W4Lem12_8) (h36 : W4Lem3_6) (h416 : W4Lem4_16)
    (hgr : CFSG.Open.GriessAllModelsStatement) (hKN : K_UC146N) (hKM : K_UC146M) :
    S17.UC2_14_6 D := by
  have : IsSimpleGroup G := D.standing.simple
  intro Y X n q hY hXY hX hSU hn6 hMY hq hq2 hqn hsig he3 r hr hr3 hrn A hAY hA hperm
  have hAM : A ≤ D.M := hAY.trans (CFSG.Open.IsSubnormal.le hY.1)
  refine Set.eq_singleton_iff_unique_mem.2
    ⟨⟨D.maxLocal, sup_le hAM D.sylowM.le⟩, fun N hN => ?_⟩
  by_contra hNM
  have hTN : D.T ≤ N := le_sup_right.trans hN.2
  have hAN : A ≤ N := le_sup_left.trans hN.2
  have hNT : N ∈ calMOf D.T := ⟨hN.1, hTN⟩
  have hrM : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
    h846 Y hY n hSU r hr hr3 hrn
  have hAU : A ∈ uniqueSet D.M := mem_uniqueSet_of_r846 h846 hY hSU hr hr3 hrn hAY hA
  have hHM : ¬ UC22.conjClosure N A ≤ D.M :=
    not_conjClosure_le_of_mem_uniqueSet D.maxLocal hN.1 hAU hNM
  have h3N : CFSG.Open.pRank 3 N ≤ 1 :=
    pRank_le_one_of_r6_6 h66 Nat.prime_three (by decide)
      (Or.inr (by rw [hsig]; rfl)) hNT hNM
  have hrN : CFSG.Open.pRank r N ≤ 1 :=
    pRank_le_one_of_r6_6 h66 hr (by omega) (Or.inl hrM) hNT hNM
  have hm3 : CFSG.Open.pRank 3 D.M = 3 := pRank_three_eq_three_of_sig hx hsig he3
  have hsN : ∀ s : ℕ, s.Prime → 3 < s → CFSG.Open.pRank s N ≤ 2 := fun s hs hs3 =>
    pRank_le_two_of_twoLocal D hx hσ3 hsig hm3 hs hs3 hN.1.1
  have hNA : N ⊓ normalizer (A : Set G) ≤ D.M :=
    inf_le_right.trans (normalizer_le_of_mem_uniqueSet D.maxLocal hAU)
  have hKNgp : CFSG.Open.IsKGroup ↥N :=
    D.standing.kProper.isKGroup N
      (CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top
        D.standing.nonab N hN.1.1)
  have hSylN : CFSG.ABGLocalTools.IsSylowOf 2 D.T N :=
    CFSG.ABGLocalTools.IsSylowOf.of_le D.sylowG hTN le_top
  have hodd : Odd n := by
    rw [Nat.odd_iff]
    omega
  have hr2 : r ≠ 2 := by omega
  rcases hKN G N D.T A D.M r hKNgp hSylN hr hr3 ⟨n, hodd, hrn⟩ hAN hA hperm h3N hrN hsN
      (sup_le hAM D.sylowM.le) hNA with h1 | ⟨hcore, hcase⟩ | ⟨E, hEM, hEE, hAE, hrE, hEA⟩
  · exact hHM h1
  · by_cases hYZ : Y ≤ centralizer (D.Z : Set G)
    · exact uc2_14_6_paraTwo h869 hY hSU hodd hr hr2 hAY hA hperm hAU hN hNM hrN hcore hYZ
    · have hYZ' : ⁅Y, D.Z⁆ ≠ ⊥ := fun hbot =>
        hYZ (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
      have hn5 : 5 ≤ n := by
        by_contra hnlt
        push Not at hnlt
        have hn1 : n = 1 := by omega
        rw [hn1] at hrn
        norm_num at hrn
        have hrle : r ≤ 3 := Nat.le_of_dvd (by norm_num : 0 < 3) hrn
        omega
      have hTH : D.T ≤ normalizer (UC22.conjClosure N A : Set G) :=
        hTN.trans (uc22p22v_le_normalizer_conjClosure N A)
      exact hHM (uc2_14_6_paraThree h869 h128 h36 h416 hgr hY hMY hSU (by omega) hYZ' hTH
        hcase)
  · exact hEA (hKM G Y A E n r hSU hr hr3 hAY hA (hEM.trans hMY) hEE hAE hrE)

theorem uc2_14_6_dataOfSetup
    (hS : RankThreeUC.Standing G) (S : RankThreeUC.Setup G)
    (h66 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_6 (Three.dataOfSetup hS S))
    (h846 : F08.R846 (Three.dataOfSetup hS S)) (h869 : F08.R869 (Three.dataOfSetup hS S))
    (h128 : W4Lem12_8) (h36 : W4Lem3_6) (h416 : W4Lem4_16)
    (hgr : CFSG.Open.GriessAllModelsStatement) (hKN : K_UC146N) (hKM : K_UC146M) :
    S17.UC2_14_6 (Three.dataOfSetup hS S) :=
  uc2_14_6_of_inputs (UC22.dataExt_ofSetup hS S) (fun _ _ hq => hq.1) h66 h846 h869 h128 h36
    h416 hgr hKN hKM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
