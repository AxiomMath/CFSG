module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ExceptionalParabolics
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviCenter
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.WeakClosure81.SixFifteen
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
  (center_eq_bot_of_simple_of_two_le_pRank)

variable {G : Type} [Group G] [Finite G]

theorem odd_and_three_le_of_is2F4 {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Quasithin.Is2F4 n X) : Odd n ∧ 3 ≤ n := by
  obtain ⟨-, -, -, -, hodd, h3⟩ := h.1
  exact ⟨hodd, h3⟩

theorem two_le_pRank_three_bar2_of_exceptional (hP : Inputs1719.K_2F4Parabolic)
    (hTi : Inputs1719.K_TitsParabolic) {L : Subgroup G}
    (hshape : (∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
      LieModel (Bar2 L) .Tits 0 2 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) := by
  rcases hshape with ⟨n, h2F4⟩ | hT
  · obtain ⟨hodd, h3⟩ := odd_and_three_le_of_is2F4 h2F4
    exact (hP (Bar2 L) n h2F4 hodd (by omega)).1.1
  · exact (hTi (Bar2 L) hT).1.ge


theorem four_le_pRank_three_M_of_not_normal (hP : Inputs1719.K_2F4Parabolic)
    (hTi : Inputs1719.K_TitsParabolic) {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnN : ¬ D.M ≤ normalizer (L : Set G))
    (hshape : (∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
      LieModel (Bar2 L) .Tits 0 2 1) :
    4 ≤ CFSG.Open.pRank 3 D.M := by
  have h2bar := two_le_pRank_three_bar2_of_exceptional hP hTi hshape
  have h2L : 2 ≤ CFSG.Open.pRank 3 L := by
    rw [← s13_pRank_bar_top Nat.prime_three (by norm_num) L]
    exact h2bar
  obtain ⟨E, hEL, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) L
  have hsimple : IsSimpleGroup (Bar2 L) := by
    rcases hshape with ⟨n, h2F4⟩ | hT
    · exact (CFSG.LieType.Simplicity.fam_2f4_simplicity (Bar2 L) 2 n h2F4).2
    · obtain ⟨-, hRT⟩ := CFSG.Blueprint.LieModel.reeTitsModel hT (by decide)
      exact (CFSG.LieType.Simplicity.fam_tits_simplicity (Bar2 L) 2 1 hRT).2
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    have hc : Subgroup.center (Bar2 L) = ⊥ :=
      @center_eq_bot_of_simple_of_two_le_pRank _ _ _ hsimple 3 Nat.prime_three h2bar
    rw [hc, Subgroup.card_bot]
    norm_num
  have h4 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.calCRankTwice D.M L hL hnN
    3 Nat.prime_three (by norm_num) hZ E hEL hEel (CFSG.Open.pRank 3 L) hEcard
  omega

theorem three_mem_sig_of_not_normal {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hP : Inputs1719.K_2F4Parabolic) (hTi : Inputs1719.K_TitsParabolic)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ D.M ≤ normalizer (L : Set G))
    (hshape : (∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
      LieModel (Bar2 L) .Tits 0 2 1) :
    3 ∈ D.sig :=
  hSg.four_mem 3 Nat.prime_three (by norm_num)
    (four_le_pRank_three_M_of_not_normal hP hTi hL hnN hshape)

theorem k_eq_one_of_not_normal {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hP : Inputs1719.K_2F4Parabolic) (hTi : Inputs1719.K_TitsParabolic)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ D.M ≤ normalizer (L : Set G))
    (hshape : (∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
      LieModel (Bar2 L) .Tits 0 2 1) :
    D.k = 1 := by
  have h3 := three_mem_sig_of_not_normal hSg hP hTi hL hnN hshape
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    UC6S846.sp_of_mem_sig hSg hns h3
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  rw [if_pos hsp]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
