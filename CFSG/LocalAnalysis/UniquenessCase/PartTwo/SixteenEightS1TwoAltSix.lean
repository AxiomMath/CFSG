module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoAltSixAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_s1_two_alt_six (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_1 D V₀ V hV L ∨ Case168_2Star D V₀ V hV L := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have hsig : D.sig = {3} :=
    s16e_two_alt6_sig_eq_three D hx h4 h61 h127 h1214 hV hset hL hs hsum
  obtain ⟨hSymK, L₀, hdir, hSymL0⟩ :=
    s16e_two_alt6_kbar_L0 D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hA hsum
  refine Or.inr ⟨hSymK, ⟨L₀, hdir, Or.inl ⟨6, by norm_num, by norm_num, hSymL0, hA, ?_⟩⟩, hsig⟩
  rw [← s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL hs]
  exact hsum

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
