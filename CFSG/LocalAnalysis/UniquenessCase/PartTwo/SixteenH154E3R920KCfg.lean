module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFact
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920ImgSyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920ImgLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920ImgNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Hyp97)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (xbar9 wbar9)

variable {G : Type} [Group G] [Finite G]

theorem kCfgL28_of_hyp97 {D : Data G} {L D₃ A : Subgroup G} (c : R920Cfg D L D₃ A)
    {Y H S : Subgroup G} (h97 : Hyp97 D Y H D₃ S) (hY : Opp 3 Y = L)
    (hSH : CFSG.ABGLocalTools.IsSylowOf 2 S H) :
    KCfgL28 (xbar9 Y H) (wbar9 D Y H)
      ((F09.img9 H S).subgroupOf (F09.img9 H (F09.L9 Y H))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYH : Y ≤ H := h97.1.2.1.1
  have hLH : L ≤ H := by
    rw [← hY]
    exact (F09.opp_le_self 3 Y).trans hYH
  have hXM : Opp 3 Y ≤ D.M := by
    rw [hY]
    exact c.le_M
  have hSM : S ≤ D.M := h97.2.2.2.le.trans h97.1.1.1
  have hker := isPGroup_ker_toImg9_of_isL2 hLH c.isL2
  refine ⟨isL2_bar2_xbar9 hY hLH c.isL2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [xbar9, wbar9]
    exact Subgroup.subgroupOf_mono _
      (Subgroup.map_mono (Subgroup.subgroupOf_mono H
        (le_inf ((F09.opp_le_self 3 Y).trans hYH) hXM)))
  · rw [wbar9]
    exact Subgroup.subgroupOf_mono _
      (Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_inf hSH.le hSM)))
  · exact isSylowOf_two_img9_subgroupOf hYH hSH
  · intro E hE hEcard
    let Kb : Subgroup (F09.Hbar9 H) := F09.img9 H (F09.L9 Y H)
    have hE' : E ≤ (F09.img9 H (Opp 3 Y)).subgroupOf Kb := by
      rw [xbar9] at hE
      exact hE
    have hEbX : E.map Kb.subtype ≤ F09.img9 H (Opp 3 Y) := by
      have h1 : E.map Kb.subtype ≤
          ((F09.img9 H (Opp 3 Y)).subgroupOf Kb).map Kb.subtype :=
        Subgroup.map_mono hE'
      rw [Subgroup.subgroupOf_map_subtype] at h1
      exact h1.trans inf_le_left
    have hEbL : E.map Kb.subtype ≤ F09.img9 H L := by
      rw [← hY]
      exact hEbX
    have hEbc : Nat.card (E.map Kb.subtype) = 3 := by
      rw [Subgroup.card_map_of_injective Kb.subtype_injective, hEcard]
    have hEbpg : IsPGroup 3 (E.map Kb.subtype) :=
      IsPGroup.of_card (n := 1) (by rw [hEbc, pow_one])
    obtain ⟨B, hBL, hBcard, hBimg⟩ :=
      exists_le_card_eq_img9_eq hLH hker Nat.prime_three (by norm_num) hEbpg hEbL
    have hN := normalizer_le_img9_of_pGroup c hLH (p := 3) (Or.inl rfl) hEbpg
      ⟨B, hBL, hBcard.trans hEbc, le_of_eq hBimg⟩
    intro q hq
    rw [wbar9, Subgroup.mem_subgroupOf]
    exact hN (Subgroup.le_normalizer_map Kb.subtype (Subgroup.mem_map_of_mem Kb.subtype hq))
  · intro B hBX hBcard P hPpg hBP
    let Kb : Subgroup (F09.Hbar9 H) := F09.img9 H (F09.L9 Y H)
    have hBX' : B ≤ (F09.img9 H (Opp 3 Y)).subgroupOf Kb := by
      rw [xbar9] at hBX
      exact hBX
    have hBbX : B.map Kb.subtype ≤ F09.img9 H (Opp 3 Y) := by
      have h1 : B.map Kb.subtype ≤
          ((F09.img9 H (Opp 3 Y)).subgroupOf Kb).map Kb.subtype :=
        Subgroup.map_mono hBX'
      rw [Subgroup.subgroupOf_map_subtype] at h1
      exact h1.trans inf_le_left
    have hBbL : B.map Kb.subtype ≤ F09.img9 H L := by
      rw [← hY]
      exact hBbX
    have hBbc : Nat.card (B.map Kb.subtype) = 7 := by
      rw [Subgroup.card_map_of_injective Kb.subtype_injective, hBcard]
    have hBbpg : IsPGroup 7 (B.map Kb.subtype) :=
      IsPGroup.of_card (n := 1) (by rw [hBbc, pow_one])
    have hPbpg : IsPGroup 7 (P.map Kb.subtype) := hPpg.map Kb.subtype
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    obtain ⟨B', hB'L, hB'card, hB'img⟩ :=
      exists_le_card_eq_img9_eq hLH hker Nat.prime_seven (by norm_num) hBbpg hBbL
    have hN := normalizer_le_img9_of_pGroup c hLH (p := 7) (Or.inr rfl) hPbpg
      ⟨B', hB'L, hB'card.trans hBbc, (le_of_eq hB'img).trans (Subgroup.map_mono hBP)⟩
    intro q hq
    rw [wbar9, Subgroup.mem_subgroupOf]
    exact hN (Subgroup.le_normalizer_map Kb.subtype (Subgroup.mem_map_of_mem Kb.subtype hq))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
