module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Y2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Opp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920OppThree
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09s
public import CFSG.LocalAnalysis.UniquenessCase.Nine24R912L2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R99
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R911

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Hyp97)

variable {G : Type} [Group G] [Finite G]

namespace R920Cfg

variable {D : Data G} {L D₃ A : Subgroup G}

omit [Finite G] in
private theorem r920chain_opp_mono (p : ℕ) {X Y : Subgroup G} (h : X ≤ Y) :
    Opp p X ≤ Opp p Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact Subgroup.closure_mono fun x hx => ⟨h hx.1, hx.2⟩

omit [Finite G] in
private theorem r920chain_opp_idem (p : ℕ) (Y : Subgroup G) : Opp p (Opp p Y) = Opp p Y := by
  refine le_antisymm (F09.opp_le_self p (Opp p Y)) ?_
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩

theorem opp_eq_of_pRank_le_one (c : R920Cfg D L D₃ A) {Y : Subgroup G} (hLY : L ≤ Y)
    (hYM : Y ≤ D.M) (hrk : CFSG.Open.pRank 3 (Opp 3 Y) ≤ 1) : Opp 3 Y = L := by
  have hLX : L ≤ Opp 3 Y := by
    rw [← c.opp_eq]
    exact r920chain_opp_mono 3 hLY
  have hXM : Opp 3 Y ≤ D.M := (F09.opp_le_self 3 Y).trans hYM
  have hN : (L.subgroupOf (Opp 3 Y)).Normal :=
    normal_of_pRank_le_one c.mem c.isL2 hLX hXM hrk
  have hX3 : Opp 3 (Opp 3 Y) = Opp 3 Y := r920chain_opp_idem 3 Y
  exact eq_of_normal_of_pRank_le_one c.isL2 hLX hN hX3 hrk

theorem exists_hyp97 (c : R920Cfg D L D₃ A) (h61 : UC6.R6_1 D) (h3 : 3 ∈ D.sig)
    (hex : ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ L ≤ N ∧ N ≠ D.M) :
    ∃ Y H S : Subgroup G, L ≤ Y ∧ Hyp97 D Y H D₃ S ∧ Opp 3 Y = L := by
  obtain ⟨Y, H, S, hLY, h97⟩ := F09.exists_hyp97_of_mem_calY2_9 D (c.mem_calY2_9 h61 h3 hex)
    (by rw [c.opp_eq]; exact c.D₃_le) c.D₃_card
  exact ⟨Y, H, S, hLY, h97, c.opp_eq_of_pRank_le_one hLY h97.1.1.1
    ((CFSG.SectionRank.pRank_mono (by norm_num) (F09.opp_le_L9 Y H)).trans h97.1.2.1.2.2.le)⟩

end R920Cfg

theorem pCoreOf_le_pCoreOf_of_le_normalizer {L Y : Subgroup G} (hLY : L ≤ Y)
    (h : Y ≤ normalizer (L : Set G)) : pCoreOf 2 L ≤ pCoreOf 2 Y :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLY)
    (h.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

structure R920Chain (D : Data G) (L D₃ A Y H S : Subgroup G) : Prop extends R920Cfg D L D₃ A where
  hyp97 : Hyp97 D Y H D₃ S
  opp_Y : Opp 3 Y = L
  syl_H : CFSG.ABGLocalTools.IsSylowOf 2 S H
  syl_HM : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)
  L_normal : (L.subgroupOf (H ⊓ D.M)).Normal

namespace R920Cfg

variable {D : Data G} {L D₃ A : Subgroup G}

theorem chain_of_hyp97 (c : R920Cfg D L D₃ A)
    (h63 : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore) (h640 : UC6.R6_40_1 D)
    {Y H S : Subgroup G} (h97 : Hyp97 D Y H D₃ S) (hY : Opp 3 Y = L) :
    R920Chain D L D₃ A Y H S := by
  have hLY : L ≤ Y := hY ▸ F09.opp_le_self 3 Y
  have hYL : Y ≤ normalizer (L : Set G) := hY ▸ F09.le_normalizer_opp_self 3 Y
  have hR : pCoreOf 2 Y ≠ ⊥ := fun h =>
    c.ne_bot (le_bot_iff.1 (h ▸ pCoreOf_le_pCoreOf_of_le_normalizer hLY hYL))
  have h912 := F09.r912L2_of_inputs D (F09.r99_holds D) (F09.r910_holds D)
    (F09.r911_of h63 D h640) (F09.r9R5_holds D) Y H D₃ S h97 3 (by norm_num) (hY ▸ c.isL2) hR
  have h5 := F09.r9R5_holds D Y H D₃ S h97
  exact ⟨c, h97, hY, h912.1, h5.2, hY ▸ h5.1⟩

end R920Cfg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
