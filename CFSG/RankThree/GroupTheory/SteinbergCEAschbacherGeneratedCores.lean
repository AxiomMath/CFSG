module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.RankThree.GroupTheory

open CFSG
open scoped Pointwise

variable {G : Type*} [Group G]

theorem assembly_pRank_eq_pRank [Finite G] (p : ℕ) (H : Subgroup G) :
    CFSG.Assembly.pRank p H = CFSG.pRank p H :=
  (CFSG.SectionRank.pRank_coe_eq_assemblyPRank p H).symm

end CFSG.RankThree.GroupTheory
