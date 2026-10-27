module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_om8_kbar (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 := by
  have hsig := s16e_two_fam_om_sig D hx h4 h61 h127 h1214 hV hset hL hs (Or.inr rfl) hOm hsum
  exact (s16e_two_fam_om_main D hx h61 h127 h1214 h638 hV hset hL hconc hs
    (by rw [hsig]; exact Set.mem_singleton 3) (Or.inr rfl) hOm hsum).1

theorem s16e_two_om8_complement (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
      IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧
        IsOMinus ↥L₀ 8 1 := by
  have hsig := s16e_two_fam_om_sig D hx h4 h61 h127 h1214 hV hset hL hs (Or.inr rfl) hOm hsum
  exact (s16e_two_fam_om_main D hx h61 h127 h1214 h638 hV hset hL hconc hs
    (by rw [hsig]; exact Set.mem_singleton 3) (Or.inr rfl) hOm hsum).2

theorem s16e_two_om8_sig (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    D.sig = {3} :=
  s16e_two_fam_om_sig D hx h4 h61 h127 h1214 hV hset hL hs (Or.inr rfl) hOm hsum

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
