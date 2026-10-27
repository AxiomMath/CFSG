module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapL3InF
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Delta
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417RankOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Swap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormalHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexFHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexWreathHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRankHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapSp4InFHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGF2Rep417Diag.Swap
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGF2Rep417

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem k_GF2Rep417_of_w4Lem4_16
    (h416 : Inputs1719.W4Lem4_16) (h43c : W3Lem45_2Chief) (hL3 : Inputs1719.K_SwapL3InF)
    (h410 : Inputs1719.W4Lem4_10) : K_GF2Rep417 := by
  intro W _ _ hW X T L n hT hL hL2 hX hgen hshape hfix A hA
  have hO2 : Inputs1719.O2Trivial X := Inputs1719.o2Trivial_iff_pCoreOf_eq_bot.2
    ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).2 hX)
  have hsq : WeakClosure81.InFSq n X := by
    have hU3 : S17.K_U3Index := S17.k_U3Index_of_normal_and_F
      Inputs1719.k_U3IndexNormal_holds S17.k_U3IndexF_holds h43c
    rcases hshape with h | h | h | ⟨hsh, t, htT, ht⟩
    · exact Inputs1719.inFSq_sup_of_rankOne h43c Inputs1719.k_L2SzAutRank_holds hU3 hL hL2 hT
        hgen (Or.inl h)
    · exact Inputs1719.inFSq_sup_of_rankOne h43c Inputs1719.k_L2SzAutRank_holds hU3 hL hL2 hT
        hgen (Or.inr (Or.inl h))
    · exact Inputs1719.inFSq_sup_of_rankOne h43c Inputs1719.k_L2SzAutRank_holds hU3 hL hL2 hT
        hgen (Or.inr (Or.inr h))
    · exact Inputs1719.inFSq_sup_of_swap h43c Inputs1719.k_SwapSp4InF_holds hL3 h410 hL hL2 hT
        hgen hsh (GF2Rep417Diag.swapsParabolics_of_actsNontrivOnDiagramIn hsh
          (GF2Rep417Diag.isSylowIn_inf_of_isComponentOf hT hL) htT ht)
  have hb : bParam L X ≤ n := by
    refine Inputs1719.bParam_le_of_fIndexSum_le h416 hW hgen hL hT hO2 hfix
      (Set.finite_singleton X) ?_ (by simp) ?_
    · intro H hH
      rw [Set.mem_singleton_iff.mp hH]
      exact ⟨le_rfl, hT.1⟩
    · rw [fIndexSum, finsum_mem_singleton]
      exact fIndex_le_iff.mpr hsq
  have hcomm := (bParam_lt_iff (Nat.succ_pos n) L X).1 (Nat.lt_succ_of_le hb) A hA
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  exact hcomm

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.UniquenessCase.UC22
