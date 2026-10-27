module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61OneMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61TwoT
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61D10Main

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_6_1 (F : FanTree Γ G) (hXi : ∃ T : Track Γ G, InXi T) (h510 : Fan510 F)
    (h511 : Fan511 F) (h512b : Fan512b F) (h514 : Fan514 F) (h53a : Fan53a F) (h53b : Fan53b F)
    (h53c : Fan53c F) (h54 : Fan54 F) (h55a : Fan55a F) (h55c : Fan55c F) (h51a : Fan51a F)
    (h57a : Fan57a F) (h58a : Fan58aT F) (hZ : ZcFin F) : Fan61 F := by
  intro h40 α z hz h3
  obtain ⟨T, z', a, r, C⟩ := P61.exists_cfg F h40 h510 h511 h53a h514 hXi hz h3
  have hr1 := C.r1
  have hr2 := C.r2
  have hadj : Γ.Adj (T.line.vert (a + 2)) (T.line.vert (a + 1)) := by
    have := T.line.adj (a + 1)
    rw [show a + 1 + 1 = a + 2 by ring] at this
    exact this.symm
  rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
  · exact P61.fan61_one F h40 h51a h53b h53c h54 h55a h55c h512b hZ C
  · have hctx := P61.ctx_of_cfg F h40 h53b h54 h512b C
    rcases F.relIndex_nbrStab_mem_two_four hadj with h | h
    · refine P61.fan61_two_d10 F h40 h510 h511 h514 h53b h55a h57a h58a C hctx fun g hg => ?_
      have h2 : ((nbrStab Γ G (T.line.vert (a + 2))).subgroupOf
          (MulAction.stabilizer G (T.line.vert (a + 2)) ⊓
            MulAction.stabilizer G (T.line.vert (a + 1)))).index = 2 := h
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mul_self_mem_of_index_two h2 ⟨g, hg⟩)
    · have hcore : T.line.IsCoreFix z' a (a + 2) (a - 2) (a + 4) := by
        have := C.core
        rwa [show a + 2 + 2 = a + 4 by ring] at this
      exact P61.fan61_two_f20 F T hcore hctx h

end CFSG.Quasithin.Fan86
