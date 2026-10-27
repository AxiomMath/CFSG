module

public import CFSG.RankThree.GF2n.Smith81.Sec216LocalLift
public import CFSG.RankThree.GF2n.Smith81.Sec220Local

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem E3L45World.v_mem_H0 [Finite G] {M Q Z B : Subgroup G}
    {z v : G} (h : E3L45World M Q Z B z v) : v ∈ H0 M Z := by
  obtain ⟨⟨x, y, hx, hy, hxz, hyz, hv⟩, -⟩ := h.hv
  have hH := h.rem.ctx.hyp
  rw [hv]
  exact mul_mem (mem_H0_of_isConj_commute hH h.hz h.hz1 hx hxz)
    (mem_H0_of_isConj_commute hH h.hz h.hz1 hy hyz)

end CFSG.RankThree.GF2n.Smith81
