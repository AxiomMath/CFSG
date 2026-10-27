module

import CFSG.Quasithin.MS93.S46I463
public import CFSG.Quasithin.MS93.S45Loc

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]
variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)}

theorem Ctx.commutator_zm_qv_le_usup_inf_zloc (c : Ctx M T L φ)
    {α β δ : Vtx (puAmalgam c.hyp.le)} (hα : IsMVtx _ α) (hδ : IsMVtx _ δ)
    (hαβ : (puAmalgam c.hyp.le).treeGraph.Adj α β)
    (hδβ : (puAmalgam c.hyp.le).treeGraph.Adj δ β) :
    ⁅ZM (puAmalgam c.hyp.le) δ, Qv _ α⁆ ≤ Usup _ δ β ⊓ Zloc c.hyp.le L α := by
  have h20 := c.hyp.hyp20
  have hd : (puAmalgam c.hyp.le).treeGraph.dist α δ ≤ 2 := by
    have := dist_triangle (puAmalgam c.hyp.le) α β δ
    rw [dist_eq_one_of_adj _ hαβ, dist_eq_one_of_adj _ hδβ.symm] at this
    exact this
  refine le_inf ?_ ?_
  · rw [Usup, zv_of_isMVtx _ hδ]
    exact Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hα hαβ)
  · exact (Subgroup.commutator_mono (S46.zm_le_vv_of_dist_le_two hδ hd) le_rfl).trans
      (c.commutator_vv_qv_le_zloc hα)

end CFSG.Quasithin.MS93.S45

