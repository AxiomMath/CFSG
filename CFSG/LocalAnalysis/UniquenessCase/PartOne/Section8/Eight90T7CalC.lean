module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Defs
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Assembly.ComponentFreeOddCores
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem r890t7c_isQuasisimple_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz X n) :
    CFSG.Open.IsQuasisimple X := by
  haveI hs : IsSimpleGroup X :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h
  have hnab := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 h
  have hc : Subgroup.center X = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.center_eq_bot_of_isSz h
  refine ⟨?_, ?_⟩
  · exact CFSG.Assembly.Dichotomy.commutator_eq_top_of_isSimpleGroup hnab
  · exact MulEquiv.isSimpleGroup
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)

theorem r890_perfInter_mem_calC {G : Type} [Group G] [Finite G] {J M N : Subgroup G} {n : ℕ}
    (hJM : J ≤ M) (hnorm : ((perfInter890 J N).subgroupOf (N ⊓ M)).Normal)
    (hSz : IsSz (Bar2 (perfInter890 J N)) n) : perfInter890 J N ∈ calC (N ⊓ M) := by
  have hle : perfInter890 J N ≤ N ⊓ M :=
    le_inf (r890_perfInter_le_right J N) ((r890_perfInter_le_left J N).trans hJM)
  refine ⟨?_, ?_, ?_⟩
  · exact CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle hnorm
  · exact r890_perfInter_perfect J N
  · exact r890t7c_isQuasisimple_of_isSz hSz

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
