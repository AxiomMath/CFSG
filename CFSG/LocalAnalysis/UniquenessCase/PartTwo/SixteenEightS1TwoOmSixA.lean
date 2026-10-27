module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_om6_sumOfNat (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have hw := s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL hs
  rwa [hw] at hsum

theorem s16e_two_om6_sig_eq_three (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    D.sig = {3} :=
  s16e_two_fam_om_sig D hx h4 h61 h127 h1214 hV hset hL hs (Or.inl rfl) hOm hsum

theorem s16e_two_om6_direct (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) (h3 : D.sig = {3}) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
        IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ IsOMinus ↥L₀ 6 1 :=
  s16e_two_fam_om_main D hx h61 h127 h1214 h638 hV hset hL hconc hs
    (by rw [h3]; exact Set.mem_singleton 3) (Or.inl rfl) hOm hsum

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
