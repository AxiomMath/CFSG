module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Small
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms


theorem k5J3_of_outer
    (h : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      CFSG.Blueprint.NativeSporadic.J3) ≤ 2) : K5J3 := by
  intro Y _ _ hq _ hJ p hp h5
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  haveI : Group.IsPerfect Y := hq.1
  obtain ⟨e⟩ := hJ
  have hinj : CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Y)
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Y)
  have hcardS : Nat.card (Y ⧸ center Y) = 50232960 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  have hOut : Nat.card (Outer (Y ⧸ center Y)) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv h e
  have hnot : ¬ p ^ 2 ∣ Nat.card (MulAut (Y ⧸ center Y)) :=
    not_sq_dvd_mulAut_of_outer_le_two hq.2.1 hcardS hOut hp h5
  have hbound : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) ≤ 1 :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd hp.one_lt hnot
  exact hinj.trans hbound

theorem k5J3_holds : K5J3 :=
  k5J3_of_outer (CFSG.Sporadic.Schreier.outer_card_le_of_equiv
    CFSG.Sporadic.SmallOddCore.j3_outer_card_le CFSG.Sporadic.Schreier.j3PermEquiv)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
