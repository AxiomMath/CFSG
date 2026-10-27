module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenCount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenPStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_mem_sig_seven_of_elem {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {r : ℕ}
    (hr : 2 ≤ r) (hr5 : r ≤ 5) (hE : IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L))
    (hsym : SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r 3) : 7 ∈ D.sig := by
  by_contra h7
  obtain ⟨Δ, σ, hctx⟩ := s16e_d3_exists_ctx D hV c.setting hs hr hr5 hE
    (by rw [s16c1610_dParam_seven]; exact hsym)
  have h3 : 3 ∈ D.sig := by
    obtain ⟨q, hq⟩ := c.std.hSg.nonempty
    rcases s168e3_seven_eq_of_mem_sig c hctx hq with rfl | rfl
    · exact hq
    · exact absurd hq h7
  have hH : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  have hk : D.k = 1 := Data.k_eq_one_of_three_mem D c.std.hSg (c.std.h1219 V₀ V hH) h3
  have hmGT : MBarGT D.M V₀ V (D.k + 1) := by
    rw [Hyp125.mBarGT_iff_lt_mBar hH (D.k + 1), hk]
    exact s168e3_seven_two_lt_mParam hctx
  obtain ⟨Y, hY⟩ := s168e3_seven_exists_inPStar c hs hr hr5 hE hsym
  exact twelve_twelve D c.std.h63 c.std.h126 c.std.h1211 c.std.h111 c.std.h6161ii hH hmGT Y hY

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
