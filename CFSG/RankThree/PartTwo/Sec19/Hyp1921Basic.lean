module

public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Late.Uniqueness
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem Hyp1921.toSec18Std (h : Hyp1921 G A M N L) : Sec18Std G A M :=
  { toPartTwoStanding := h.toSec19Std.toPartTwoStanding
    partTwoS_eq := h.partTwoS_eq
    mem_partTwoE := h.mem_partTwoE
    mem_scriptM := h.mem_scriptM }

theorem Hyp1921.isE27 (h : Hyp1921 G A M N L) : IsE27 A :=
  isE27_of_mem_partTwoE h.mem_partTwoE

theorem Hyp1921.le_N (h : Hyp1921 G A M N L) : A ≤ N :=
  h.mem_scriptM_N.2

theorem Hyp1921.le_M (h : Hyp1921 G A M N L) : A ≤ M :=
  le_of_mem_scriptM_gamma h.isE27 h.mem_scriptM

theorem Hyp1921.L_le_N (h : Hyp1921 G A M N L) : L ≤ N :=
  le_of_mem_oTwoComponentsIn h.mem_oTwoComponentsIn

end CFSG.RankThree.PartTwo.Late
