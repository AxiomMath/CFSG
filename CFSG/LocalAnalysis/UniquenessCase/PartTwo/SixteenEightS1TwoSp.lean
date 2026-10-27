module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoSpA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_s1_two_sp (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  have hwstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D (r1217_of_twelve_seventeen D hx h61 h127 h1214)
      hset.hyp151 hV hL hs
  have hsumTop : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
    rw [← hwstar]
    exact hsum
  refine ⟨s16e_two_sp_kbar_sym D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hSp hsum,
    ⟨lBar V₀ V hV L, ?_, ?_⟩,
    s16e_two_sp_sig D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hSp hsum⟩
  · exact s16e_two_sp_lbar_direct D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hSp hsum
  · exact Or.inr (Or.inr (Or.inl ⟨hSp, hSp, hsumTop⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
