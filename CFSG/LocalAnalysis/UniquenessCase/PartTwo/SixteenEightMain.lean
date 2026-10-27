module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_8_four_concl168 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h638 : UC6.R6_38 D) (h1110 : R1110Core D) (h164 : R16_4 D) (h165 : R16_5 D)
    (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D) (h111 : W3Thm111 G)
    (h6161ii : W3Lem616_1ii G) (h77 : F07.R77Eq D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h167 : ¬ Concl167 D V₀ V hV L)
    (h163 : s15 D.M V₀ V hV L = 1 ∨ gamma15 D.M V₀ V hV L ≤ 3 → Concl163 D V₀ V hV L) :
    Concl168 D V₀ V hV L := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  by_cases hs : s15 D.M V₀ V hV L = 1
  · exact concl168_of_four
      (s16e_s1_survivors D hx h4 hSg h61 h127 h1214 h638 h1110 h164 h165 h63 h126 h1211 h111
        h6161ii h77 h1219 hV hset hL hconc h167 hs (h163 (Or.inl hs)))
  · have hs1 : 1 < s15 D.M V₀ V hV L := by
      have := Om8Excl.one_le_s15 D.M V₀ V hV L
      omega
    have h164' := h164 V₀ V L hV hset hconc hs1
    have hγ3 : gamma15 D.M V₀ V hV L ≤ 3 := by
      rcases h164'.2 with h | h | h | h
      · exact h
      · exact (s16e_not_case164_2 hx h4 h).elim
      · exact (s16e_not_case164_3 hx h4 h).elim
      · exact (s16e_not_case164_4 hx h4 h).elim
    exact s16e_s2_concl168 D hx h4 h61 h127 h1217 hV hset hL hconc (h163 (Or.inr hγ3)) h164'

theorem r16_8_four_holds (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h638 : UC6.R6_38 D) (h1110 : R1110Core D) (h163 : R16_3 D) (h164 : R16_4 D)
    (h165 : R16_5 D) (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D)
    (h111 : W3Thm111 G) (h6161ii : W3Lem616_1ii G) (h77 : F07.R77Eq D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) : R16_8 D := by
  intro V₀ V L hV hset hL hconc hall
  exact ⟨L, hset, hL, hconc,
    r16_8_four_concl168 D hx h4 hSg h61 h127 h1214 h638 h1110 h164 h165 h63 h126 h1211 h111
      h6161ii h77 h1219 hV hset hL hconc (hall L hset hL hconc)
      (fun _ => h163 V₀ V L hV hset hL hconc)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
