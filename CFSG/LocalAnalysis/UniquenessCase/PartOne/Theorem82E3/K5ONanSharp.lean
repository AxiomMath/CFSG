module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.K5Sharp
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneON
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.Sporadic.ON

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k5ONanSharp_holds :
    K5ONanSharp := by
  intro Y _ _ hThree p hp h5 hp7
  obtain ⟨hq, -, hSpor⟩ := hThree
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hq.1
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  obtain ⟨e⟩ := hSpor
  haveI hS : IsSimpleGroup (Y ⧸ center Y) := hq.2
  have hcardS : Nat.card (Y ⧸ center Y) = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  have hnab : ∃ a b : Y ⧸ center Y, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    haveI : IsMulCommutative (Y ⧸ center Y) := ⟨⟨fun a b => hc a b⟩⟩
    have hprime := (Group.is_simple_iff_prime_card (α := Y ⧸ center Y)).1 hS
    rw [hcardS] at hprime
    norm_num at hprime
  have hinj : CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Y)
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Y)
  have hnot : ¬ p ^ 2 ∣ Nat.card (MulAut (Y ⧸ center Y)) :=
    CFSG.RankThree.PartOne.not_sq_dvd_card_mulAut_ONan hnab e hp (by omega) hp7
  exact hinj.trans
    (CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd hp.one_lt hnot)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
