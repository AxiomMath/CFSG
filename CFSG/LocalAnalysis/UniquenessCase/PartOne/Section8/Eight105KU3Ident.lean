module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3IdentBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3IdentOrders
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3CensusSub
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3Census

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kU3Ident_of_census (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hK32 : UCK.K32)
    (hOdd : KU3CensusOdd) (hL2 : KU3CensusL2) (hU3 : KU3CensusU3) : KU3Ident := by
  intro Y _ _ hY hO X K D₀ n p _hXnorm hX3 hXeq hK hL2K hn hnEven hp hpdiv hD₀K hD₀p hcent hXneK
  have hKX : K ≤ X := by rw [hXeq]; exact Subgroup.le_normalClosure
  have hKne : K ≠ ⊥ := by
    intro hbot
    apply hXneK
    rw [hXeq, hbot]
    exact le_antisymm (Subgroup.normalClosure_le_normal (by simp)) bot_le
  obtain ⟨hSimple, a, b, hnonab⟩ :=
    isSimpleGroup_of_normalClosure hSch hY hO (le_of_eq hX3) hXeq hK hKne
  have hRank : Open.pRank 3 (⊤ : Subgroup ↥X) = 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup X, hX3]
  have hKGroup : CFSG.Open.IsKGroup ↥X := hY.subgroup X
  have hHyp : KU3CensusHyp (K.subgroupOf X) (D₀.subgroupOf X) n p :=
    kU3CensusHyp_subgroupOf hKX hK hL2K hn hnEven hp hpdiv hD₀K hD₀p hcent hXneK
  have hperf' : ⁅K.subgroupOf X, K.subgroupOf X⁆ = K.subgroupOf X := hHyp.1
  have hL2' : IsL2 (Bar2 (K.subgroupOf X)) (2 * n) := hHyp.2.1
  have hm : 4 ≤ 2 * n := by omega
  rcases hK32 ↥X hKGroup hSimple ⟨a, b, hnonab⟩ hRank with
    ⟨r, f, hLie⟩ | ⟨r, f, hmod, hLie⟩ | ⟨r, f, hmod, hLie⟩ | hSpor
  · by_cases hr : r = 2
    · rw [hr] at hLie
      exact absurd hHyp (hL2 ↥X f hLie (K.subgroupOf X) (D₀.subgroupOf X) n p)
    · exact absurd hL2' (hOdd ↥X r f hr (Or.inl hLie) (K.subgroupOf X) hperf' (2 * n) hm)
  · by_cases hr : r = 2
    · rw [hr] at hLie hmod
      exfalso
      exact false_of_psl_three_two_odd hLie hmod (K.subgroupOf X) n hL2'
    · exact absurd hL2' (hOdd ↥X r f hr (Or.inr (Or.inl ⟨hmod, hLie⟩)) (K.subgroupOf X) hperf'
        (2 * n) hm)
  · by_cases hr : r = 2
    · rw [hr] at hLie hmod
      have hfEven : Even f := CFSG.StandardType.TwoThree.even_of_two_pow_mod hmod
      have hf : f = 2 * n := hU3 ↥X f hfEven hLie (K.subgroupOf X) (D₀.subgroupOf X) n p hHyp
      rw [hf] at hLie
      exact hLie
    · exact absurd hL2' (hOdd ↥X r f hr (Or.inr (Or.inr ⟨hmod, hLie⟩)) (K.subgroupOf X) hperf'
        (2 * n) hm)
  · exfalso
    exact false_of_isSpor_j1 hSpor (K.subgroupOf X) hm hL2'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
