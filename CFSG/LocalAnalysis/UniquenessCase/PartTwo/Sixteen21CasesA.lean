module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Order
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen21

theorem one_le_pRank_of_case2 {D : Data G} (h1217 : R1217 D) (hSg : UC6S846.SigmaStd D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_2 D V₀ V hV L) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 7 (D.M ⊓ centralizer ({v} : Set G)) := by
  have h7 : 7 ∈ D.sig := by rw [hc.2.2.2]; exact Set.mem_singleton 7
  exact one_le_pRank_of_not_dvd_mbar hV hS.setting.hyp16 (p := 7) (k := 3) (by norm_num)
    (by norm_num) (D.sig_rank 7 h7) (hSg.three_le 7 h7)
    (c23_not_dvd_card_mbar_case2 D h1217 hS hc)

theorem one_le_pRank_of_case3 {D : Data G} (h1217 : R1217 D) (hSg : UC6S846.SigmaStd D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_3 D V₀ V hV L) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
  have h3 : 3 ∈ D.sig := by rw [hc.2.2.2]; exact Set.mem_singleton 3
  exact one_le_pRank_of_not_dvd_mbar hV hS.setting.hyp16 (p := 3) (k := 3) (by norm_num)
    (by norm_num) (D.sig_rank 3 h3) (hSg.three_le 3 h3)
    (c23_not_dvd_card_mbar_case3 D h1217 hS hc)

theorem one_le_pRank_of_case6 {D : Data G} (h165 : R16_5 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_6 D V₀ V hV L) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
  obtain ⟨hsig, h3⟩ := h165 V₀ V L hV hS.setting hS.ne_bot hS.conc hc.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have h3mem : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  exact one_le_pRank_of_mem_cTilde hS.setting.hyp16.hyp125.1
    (card_le_four_of_hyp16 hS.setting.hyp16) Nat.prime_three (by norm_num)
    (D.sig_rank 3 h3mem) y.2 ((Subgroup.orderOf_coe y).trans hyord)

end Sixteen21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
