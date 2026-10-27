module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_sp_kbar_sym (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 := by
  have hsig := s16e_two_fam_sp_sig D hx h4 h61 h127 h1214 hV hset hL hs hSp hsum
  exact (s16e_two_fam_sp_main D hx h61 h127 h1214 h638 hV hset hL hconc hs
    (by rw [hsig]; exact Set.mem_singleton 3) hSp hsum).1

theorem s16e_two_sp_lbar_direct (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsInternalDirect (kBar D.M V₀ V hV L) (lBar V₀ V hV L) (Mbar D.M V₀ V hV) := by
  have hsig := s16e_two_fam_sp_sig D hx h4 h61 h127 h1214 hV hset hL hs hSp hsum
  exact (s16e_two_fam_sp_main D hx h61 h127 h1214 h638 hV hset hL hconc hs
    (by rw [hsig]; exact Set.mem_singleton 3) hSp hsum).2

theorem s16e_two_sp_sig (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    D.sig = {3} :=
  s16e_two_fam_sp_sig D hx h4 h61 h127 h1214 hV hset hL hs hSp hsum

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
