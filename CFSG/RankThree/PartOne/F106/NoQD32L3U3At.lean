module

public import CFSG.RankThree.PartOne.F106.NoQD32
public import CFSG.RankThree.PartOne.F106.NoQD32L3U3

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG.Assembly.LowTwoRank

theorem noQD32AtThree_of_psu6
    (hU6 : ∀ (T : Type) [Group T], StatedClassicalModel T .PSU 6 2 1 →
      ∀ E R : Subgroup T, IsElementaryAbelian 3 E → InducesQD32 E R → False) :
    NoQD32AtThree := by
  intro T _ hT E R hE h
  rcases hT with ⟨f, hf⟩ | ⟨f, hf⟩ | hT
  · exact false_psl3_qd32 hf hE h
  · exact false_psu3_qd32 hf hE h
  · exact hU6 T hT E R hE h

end CFSG.RankThree.PartOne.F106
