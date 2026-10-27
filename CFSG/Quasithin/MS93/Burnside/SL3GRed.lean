module

public import CFSG.Quasithin.MS93.S43FC1

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

section WStar

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] noncomputable def burnsideSL3G_wStar (β : Vtx X) : Subgroup X.Universal :=
  ⨆ y ∈ {y : Vtx X | IsMVtx X y ∧ X.treeGraph.dist β y < critDist X}, ZM X y

variable {X}

theorem burnsideSL3G_zm_le_wStar {β y : Vtx X} (hy : IsMVtx X y)
    (hd : X.treeGraph.dist β y < critDist X) : ZM X y ≤ burnsideSL3G_wStar X β :=
  le_iSup₂_of_le (f := fun y (_ : y ∈ {y : Vtx X | IsMVtx X y ∧
    X.treeGraph.dist β y < critDist X}) => ZM X y) y ⟨hy, hd⟩ le_rfl

theorem burnsideSL3G_wStar_le_qv (β : Vtx X) : burnsideSL3G_wStar X β ≤ Qv X β :=
  iSup₂_le fun y hy => zm_le_qv_of_dist_lt X hy.1 (by rw [tdist_comm]; exact hy.2)

end WStar

section Flat

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSL3G_zm_le_flat_of_dist_le (h : PUHyp M T L) (hU : IsSL3U M T L)
    {y δ : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y) (hδ : IsMVtx _ δ)
    (hd : (puAmalgam h.le).treeGraph.dist y δ ≤ critDist (puAmalgam h.le)) :
    ZM (puAmalgam h.le) y ≤ S34F.flat h δ := by
  by_cases hZ : ZM (puAmalgam h.le) y ≤ Qv _ δ
  · exact hZ.trans (S43F.qv_le_flat h hδ)
  · have hlt : ¬ (puAmalgam h.le).treeGraph.dist y δ < critDist (puAmalgam h.le) :=
      fun hlt => hZ (zm_le_qv_of_dist_lt _ hy hlt)
    exact S34F.zm_le_flat h hU ⟨hy, by omega, hZ⟩

theorem burnsideSL3G_wStar_le_flat (h : PUHyp M T L) (hU : IsSL3U M T L)
    {β δ : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj β δ)
    (hδ : IsMVtx _ δ) : burnsideSL3G_wStar (puAmalgam h.le) β ≤ S34F.flat h δ := by
  refine iSup₂_le fun y hy => ?_
  refine burnsideSL3G_zm_le_flat_of_dist_le h hU hy.1 hδ ?_
  have htri := dist_triangle (puAmalgam h.le) y β δ
  rw [tdist_comm _ y β, dist_eq_one_of_adj _ hβδ] at htri
  have := hy.2
  omega

end Flat

end CFSG.Quasithin.MS93.S4L
