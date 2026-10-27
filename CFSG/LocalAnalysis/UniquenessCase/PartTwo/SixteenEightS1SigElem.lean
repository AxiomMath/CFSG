module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_mem_sig_of_elem (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1110 : R1110Core D)
    (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D) (h111 : W3Thm111 G)
    (h6161ii : W3Lem616_1ii G) (h77 : F07.R77Eq D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 2 ≤ r)
    (hE : IsElemAbelianOfRank p r ↥(lBar V₀ V hV L))
    (hsym : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r (dParam p)) :
    p ∈ D.sig := by
  by_cases hsm : p = 3 ∧ r ≤ 13
  · obtain ⟨rfl, hr13⟩ := hsm
    rw [s16c1610_dParam_three] at hsym
    exact s16e_mem_sig_three_of_symSum D hx h4 h61 h127 hset.hyp16 hV hr13 hsym
  · by_cases h6 : 6 ≤ r
    · exact s16e_mem_sig_of_elem_core D hSg h127 h1110 hV hset hconc hs hp h6 hE
    · have hp7 : p = 7 := by
        rcases hp with rfl | rfl
        · exact absurd ⟨rfl, by omega⟩ hsm
        · rfl
      subst hp7
      exact s16e_d3_mem_sig_seven D hx h4 hSg h61 h127 h1110 h63 h126 h1211 h111 h6161ii h77
        h1219 hV hset hconc hs hr (by omega) hE hsym

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
