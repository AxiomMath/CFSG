module

public import CFSG.CGT.PushingUpLit.CGT6.SixThreeCore
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.CGT.PushingUpLit.BlocksCommuteDefs
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R911a
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.CGT.PushingUpLit (oTwoIn jIn)
open CFSG.LieType.BorelTits (le_normalizer_pCoreOf le_pCoreOf_of_le_normalizer)

variable {G : Type} [Group G] [Finite G]

theorem r911_of (h63 : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore) (D : Data G)
    (h640 : UC6.R6_40_1 D) : R911 D := by
  intro Y hY hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := D.standing.simple
  have hXY : Opp 3 Y ≤ Y := opp_le_self 3 Y
  have hYX : Y ≤ normalizer (Opp 3 Y : Set G) := le_normalizer_opp_self 3 Y
  have hR : pCoreOf 2 Y ≠ ⊥ := by
    intro h
    refine CFSG.CGT.PushingUpLit.ThreeFromEight.oTwoIn_ne_bot_of_isShortGroup hX.1
      (le_bot_iff.1 ?_)
    rw [← h]
    exact le_pCoreOf_of_le_normalizer 2 ((CFSG.CGT.PushingUpLit.oTwoIn_le _).trans hXY)
      (hYX.trans (CFSG.CGT.PushingUpLit.normalizer_le_normalizer_oTwoIn _))
      (CFSG.CGT.PushingUpLit.isPGroup_oTwoIn _)
  obtain ⟨H, hH, hJX, hRC⟩ := exists_mem_calMOf_isSylowOf_centralizerModCore D hY hR
  have hXH : Opp 3 Y ≤ H := hXY.trans hH.2
  have hRJ := CFSG.CGT.PushingUpLit.normalizer_le_normalizer_jIn (pCoreOf 2 Y)
  have hXR : Opp 3 Y ≤ normalizer (pCoreOf 2 Y : Set G) := hXY.trans (le_normalizer_pCoreOf 2 Y)
  have hXJ : Opp 3 Y ≤ normalizer (jIn (pCoreOf 2 Y) : Set G) := hXR.trans hRJ
  have hin : CFSG.CGT.PushingUpLit.InClassXGIn H (Opp 3 Y) :=
    CFSG.CGT.PushingUpLit.inClassXGIn_of_sylow hXH hX (CFSG.ABGLocalTools.isSylowOf_iff.1 hRC)
      ⟨hXR, ((normal_subgroupOf_iff_le_normalizer (le_inf hXR hXH)).2
        fun g hg => hJX ⟨hg.2, hRJ hg.1⟩).isSubnormal⟩
      (Or.inr ⟨hXJ, ((normal_subgroupOf_iff_le_normalizer (le_inf hXJ hXH)).2
        fun g hg => hJX ⟨hg.2, hg.1⟩).isSubnormal⟩)
  obtain ⟨L, -, hLH, hLs, hLX, -⟩ := h63.rel
    (CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple (D.standing.kProper.isKGroup H
        (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hH.1.1)))
    (CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP.1 (D.standing.charTwo H hH.1.1)) hin
  exact h640 H hH.1 (L.subgroupOf H)
    ⟨hLs, CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv (subgroupOfEquivOfLe hLH).symm hLX⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
