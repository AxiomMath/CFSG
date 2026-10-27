module

public import CFSG.Quasithin.Vol2.Ch3Sec1Defs

public section

namespace CFSG.Quasithin.SimsD1

theorem isSQTKSub_of_isSQTKCat {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h : CFSG.SectionRank.IsSQTKCat ↥H) : IsSQTKSub H := by
  refine ⟨h.2, fun p hp hp2 => ?_⟩
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p ↥H]
  exact h.1 p hp hp2

end CFSG.Quasithin.SimsD1
