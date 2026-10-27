module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoOmEightAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_s1_two_om_eight (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  have hK : IsSym ↥(kBar D.M V₀ V hV L) 3 :=
    s16e_two_om8_kbar D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hOm hsum
  obtain ⟨L₀, hdir, hO⟩ :=
    s16e_two_om8_complement D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hOm hsum
  have hsig : D.sig = {3} :=
    s16e_two_om8_sig D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hOm hsum
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have hw : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL hs
  have hsum' : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
    have h := hsum
    rwa [hw] at h
  exact ⟨hK, ⟨L₀, hdir, Or.inr (Or.inr (Or.inr (Or.inr ⟨hO, hOm, hsum'⟩)))⟩, hsig⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
