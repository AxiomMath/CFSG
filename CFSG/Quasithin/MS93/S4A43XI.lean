module

public import CFSG.Quasithin.MS93.S4A43XH

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Transport

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem vv_le_vv_smul_sup {x μ : Vtx X}
    (hN : stab X x ≤ Subgroup.normalizer ((Vv X μ ⊔ Vv X x : Subgroup X.Universal) :
      Set X.Universal))
    {k : X.Universal} (hk : k ∈ stab X x) : Vv X μ ≤ Vv X (k • μ) ⊔ Vv X x := by
  have heq : (Vv X μ ⊔ Vv X x).map (MulAut.conj k).toMonoidHom = Vv X μ ⊔ Vv X x :=
    map_conj_eq_of_mem_normalizer (hN hk)
  have hkx : k • x = x := (mem_stab _).mp hk
  rw [Subgroup.map_sup, ← vi_smul, ← vi_smul, hkx] at heq
  rw [heq]
  exact le_sup_left

end Transport

namespace Ctx43

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx43 h φ)
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem not_mem_nablaSet_geo_four {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    geo 𝔛 α' α 2 ∉ nablaSet h.le L (geo 𝔛 α' α 4) := by
  intro hmem
  have hb8 := c.eight_le_critDist
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  have hxM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hyM := c.isMVtx_geo_rev hs (i := 2) (by omega) (by decide)
  have hdxy : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) (geo 𝔛 α' α 2) = 2 := by
    rw [tdist_comm, dist_geo_geo _ (by omega) (by omega)]
  have hxy : geo 𝔛 α' α 4 ∈ nablaSet h.le L (geo 𝔛 α' α 2) :=
    (c.nabla_symm hxM hdxy).mp hmem
  obtain ⟨x', hsx⟩ := c.star_at hxM
  have hN := (c.concl437_i hsx hdxy hxy).1
  have h43 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 3) := (c.adj_geo_rev hs (i := 3) (by omega)).symm
  have h45 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) := c.adj_geo_rev hs (i := 4) (by omega)
  obtain ⟨k, hk, hk3⟩ := exists_mem_stab_smul _ h43 h45
  have hV := vv_le_vv_smul_sup _ hN hk
  have h32 : 𝔄 (geo 𝔛 α' α 3) (geo 𝔛 α' α 2) := (c.adj_geo_rev hs (i := 2) (by omega)).symm
  have hξ : 𝔄 (geo 𝔛 α' α 5) (k • geo 𝔛 α' α 2) := by
    have := (adj_smul _ k _ _).mpr h32
    rwa [hk3] at this
  have hξM : IsMVtx 𝔛 (k • geo 𝔛 α' α 2) := (isMVtx_smul _ k _).mpr hyM
  have hd5 := c.dist_geo_rev hs (i := 5) (by omega)
  have hd4 := c.dist_geo_rev hs (i := 4) (by omega)
  have hVξ : Vv 𝔛 (k • geo 𝔛 α' α 2) ≤ Qv 𝔛 α := by
    refine vv_le_qv_of_dist h hξM ?_
    have := dist_triangle (puAmalgam h.le) (k • geo 𝔛 α' α 2) (geo 𝔛 α' α 5) α
    have h5 : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 5) α = critDist 𝔛 - 5 := by
      rw [tdist_comm]; exact hd5
    rw [dist_eq_one_of_adj _ hξ.symm, h5] at this
    omega
  have hVx : Vv 𝔛 (geo 𝔛 α' α 4) ≤ Qv 𝔛 α :=
    vv_le_qv_of_dist h hxM (by rw [tdist_comm, hd4]; omega)
  apply c.not_zm_le_qv hs
  refine le_trans ?_ ((hV.trans (sup_le hVξ hVx)))
  rw [← zv_of_isMVtx _ (c.crit_symm hs).1]
  exact zv_le_vv h (by rw [tdist_comm, dist_geo _ (by omega)])

theorem star_of_crit {z w : Vtx 𝔛} (hc : IsCritical 𝔛 z w) : Star 𝔛 w z := by
  have hb6 := c.b6
  have hcw : IsCritical 𝔛 w z := ms22_iii _ h.hyp20 h.critDist_pos c.cent hc
  refine ⟨hcw, ?_⟩
  have hd : (puAmalgam h.le).treeGraph.dist w z = critDist 𝔛 := hcw.2.1
  have hm : IsMVtx 𝔛 (geo 𝔛 w z 2) := isMVtx_geo_two _ h.hyp20 h.critDist_pos hcw
  have hdm : (puAmalgam h.le).treeGraph.dist (geo 𝔛 w z 2) w = 2 := by
    rw [tdist_comm, dist_geo _ (by omega)]
  have hwm : w ∈ nablaSet h.le L (geo 𝔛 w z 2) := c.mem_nablaSet_geo_two' hc
  have hmw : geo 𝔛 w z 2 ∈ nablaSet h.le L w := (c.nabla_symm hm hdm).mp hwm
  obtain ⟨m', hsm⟩ := c.star_at hm
  have hN := (c.concl437_i hsm hdm hmw).1
  have hm1 : 𝔄 (geo 𝔛 w z 2) (geo 𝔛 w z 1) := (adj_geo _ (i := 1) (by omega)).symm
  have hm3 : 𝔄 (geo 𝔛 w z 2) (geo 𝔛 w z 3) := adj_geo _ (i := 2) (by omega)
  obtain ⟨k, hk, hk1⟩ := exists_mem_stab_smul _ hm1 hm3
  have hV := vv_le_vv_smul_sup _ hN hk
  have hw1 : 𝔄 (geo 𝔛 w z 1) w := (adj_geo_one _ (by omega)).symm
  have hkw : 𝔄 (geo 𝔛 w z 3) (k • w) := by
    have := (adj_smul _ k _ _).mpr hw1
    rwa [hk1] at this
  have hwM : IsMVtx 𝔛 w := hcw.1
  have hkwM : IsMVtx 𝔛 (k • w) := (isMVtx_smul _ k _).mpr hwM
  have hz2 : geo 𝔛 z w 2 = geo 𝔛 w z (critDist 𝔛 - 2) := by
    have hdzw : (puAmalgam h.le).treeGraph.dist z w = critDist 𝔛 := hc.2.1
    rw [← geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist z w by omega), hdzw]
  have hd3 : (puAmalgam h.le).treeGraph.dist (geo 𝔛 w z 3) (geo 𝔛 z w 2) = critDist 𝔛 - 5 := by
    rw [hz2, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hd2 : (puAmalgam h.le).treeGraph.dist (geo 𝔛 w z 2) (geo 𝔛 z w 2) = critDist 𝔛 - 4 := by
    rw [hz2, dist_geo_geo _ (by omega) (by omega)]
    omega
  refine hV.trans (sup_le (vv_le_qv_of_dist h hkwM ?_) (vv_le_qv_of_dist h hm (by omega)))
  have := dist_triangle (puAmalgam h.le) (k • w) (geo 𝔛 w z 3) (geo 𝔛 z w 2)
  rw [dist_eq_one_of_adj _ hkw.symm, hd3] at this
  omega

end Ctx43

end CFSG.Quasithin.MS93.S4A
