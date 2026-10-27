module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoOmSixA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_s1_two_om_six (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  have h3 : D.sig = {3} :=
    s16e_two_om6_sig_eq_three D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hOm hsum
  obtain ⟨hK, L₀, hdir, hO⟩ :=
    s16e_two_om6_direct D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hOm hsum h3
  have hsum' : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 :=
    s16e_two_om6_sumOfNat D hx h61 h127 h1214 hV hset hL hs hsum
  refine ⟨hK, ⟨⟨L₀, hdir, ?_⟩, h3⟩⟩
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hO, hOm, hsum'⟩)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
