module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Cyc
public import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5Opp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5CalH
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddComm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OppThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem r9_19A5_of_inputs (D : Data G) (h71 : F07.R71 D)
    (h3 : ∀ N : Subgroup G, IsTwoLocal N → ¬ N ≤ D.M → CFSG.Open.pRank 3 (N ⊓ D.M) ≤ 3)
    (hK : UCK.K332Cyc) : R9_19A5 D := by
  intro hsp5 L D₃ Y H hyp hA5 hLY _ hH
  obtain ⟨hL, hD₃L, hD₃, hD₃U, hYM, hLeq, hnorm, hidx, hHtop, hYH, hHM⟩ := hyp
  have hLY' : L ⊓ Y = L := inf_eq_left.2 hLY
  have hnorm' : (L.subgroupOf Y).Normal := by simpa only [hLY'] using hnorm
  have hidx' : ∃ k : ℕ, (L.subgroupOf Y).index = 2 ^ k := by simpa only [hLY'] using hidx
  have hOpp : Opp 3 Y = L := opp_three_eq_of_le hL hA5 hLY hnorm' hidx'
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hL.1
  have hY9 : Y ∈ F09.calY9 D := by
    refine ⟨hYM, ?_, ?_⟩
    · rintro hEq
      obtain hHN | ⟨N, hNcoatom, hHN⟩ := IsCoatomic.eq_top_or_exists_le_coatom H
      · exact hHtop hHN
      · have hNmem : N ∈ calNOf Y := ⟨hNcoatom, hYH.trans hHN⟩
        rw [hEq, Set.mem_singleton_iff] at hNmem
        exact hHM (hHN.trans hNmem.le)
    · intro A hAY hAcard
      have hAL : A ≤ L := by
        intro a ha
        have ha3 : a ^ 3 = 1 := by
          have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩))
          simpa [hAcard] using h
        exact mem_of_pow_eq_one_of_index_two_pow hnorm' hidx' (p := 3) (a := 1) (by decide)
          (hAY ha) (by simpa using ha3)
      obtain ⟨l, hlL, hAeq⟩ := exists_eq_map_conj_of_card_three hA5 hD₃L hD₃ hAL hAcard
      rw [hAeq]
      exact PartTwo.conj_mem_uniqueSet hD₃U (hLM hlL)
  have hMOf : calMOf Y ≠ {D.M} := by
    intro hEq
    have hHmem : H ∈ calMOf Y := ⟨hH, hYH⟩
    rw [hEq, Set.mem_singleton_iff] at hHmem
    exact hHM hHmem.le
  have hSub : calMOf Y ⊆ F09.calH9 D Y ∪ {D.M} := by
    intro N hN
    by_cases hNM : N = D.M
    · exact Or.inr (Set.mem_singleton_iff.mpr hNM)
    · have hNtop : N ≠ ⊤ := by
        have := D.standing.simple
        exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1
      have hNnotM : ¬ N ≤ D.M := by
        intro hle
        exact hNM (hN.1.2 D.M D.maxLocal.1 hle).symm
      have hypN : PartTwo.Hyp919c D L D₃ Y N :=
        ⟨hL, hD₃L, hD₃, hD₃U, hYM, hLeq, hnorm, hidx, hNtop, hN.2, hNnotM⟩
      exact Or.inl (mem_calH9 h71 hK hsp5 (h3 N hN.1.1 hNnotM) hypN hA5 hLY
        (CFSG.PreuniquenessRankFour.Helpers.twoLocal_pCoreOf_ne_bot hN.1.1))
  have hComm : ∀ A ∈ F09.Inv9' D.M Y 3, ⁅A, Opp 3 Y⁆ ≤ pCoreOf 2 A := by
    intro A hA
    have hs : IsSimpleGroup (Bar2 L) := PartTwo.S19.isSimpleGroup_bar2_of_isAlt_five hA5
    have h3dvd : 3 ∣ Nat.card (Bar2 L) := PartTwo.S19.three_dvd_bar2_of_isAlt hA5
    have hLX : L = L ⊔ pCoreOf 2 L := by simpa only [hLY'] using hLeq
    rw [hOpp]
    exact PartOne.Section9.comm_le_pCoreOf hL le_rfl
      (PartTwo.opp_three_eq_self_of_bar2 hL hs h3dvd) hLX hs h3dvd hA.1 hA.2.1
      (hLY.trans hA.2.2)
  exact ⟨hY9, hMOf, hSub, hComm, by simpa only [hOpp] using hidx'⟩

theorem r9_19A5_dataOfSetup (hS : Standing G) (S : Setup G)
    (h63 : UC6.R6_3 (PartTwo.Three.dataOfSetup hS S)) (hK : UCK.K332Cyc) :
    R9_19A5 (PartTwo.Three.dataOfSetup hS S) :=
  r9_19A5_of_inputs _ (PartTwo.Three.r71_dataOfSetup hS S h63)
    (fun _ _ _ => (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) inf_le_right).trans
      (PartTwo.Three.pRank_le_three_dataOfSetup hS S Nat.prime_three (by norm_num) le_rfl)) hK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5
