module

public import CFSG.Quasithin.MS93.S46I466aQC2

public section

namespace CFSG.Quasithin.MS93.S46.QMix

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I466b
open scoped Matrix commutatorElement

section Orbit

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem commutator_vv_inf_qv_zm_smul_le (hfull : IsSL3Full M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {x y : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    (hx : IsMVtx _ x) (hxy : (puAmalgam h.le).treeGraph.dist y x = 2)
    (hC1 : ⁅Qv (puAmalgam h.le) y, Ltil h.le L y⁆ ≤ Vv _ y)
    (hI : ⁅Vv (puAmalgam h.le) y, Vv _ y⁆ ≤ Zloc h.le L y) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab (puAmalgam h.le) y) :
    ⁅Vv (puAmalgam h.le) x ⊓ Qv _ y, ZM _ (g • x)⁆ ≤ Zloc h.le L y := by
  have h20 := h.hyp20
  have hyρ : (puAmalgam h.le).treeGraph.Adj y (geo _ y x 1) := adj_geo_one _ (by omega)
  have hρx : (puAmalgam h.le).treeGraph.Adj (geo _ y x 1) x := by
    have := adj_geo (puAmalgam h.le) (u := y) (w := x) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist y x ≤ 1 + 1)] at this
  obtain ⟨l, hl, hlx⟩ := exists_ltil_smul_eq h hfull hy hyρ hρx hg
  rw [← hlx]
  have hlx' : IsMVtx (puAmalgam h.le) (l • x) := (isMVtx_smul _ l x).mpr hx
  have hd : (puAmalgam h.le).treeGraph.dist y (l • x) = 2 := by
    have hls : l • y = y := (mem_stab _).mp (ltil_le_stab h y hl)
    rw [← dist_smul _ l y x, hls] at hxy
    exact hxy
  have hZV : ZM (puAmalgam h.le) (l • x) ≤ Vv _ y := by
    have := zv_le_vv_of_dist h (le_of_eq hd)
    rwa [zv_of_isMVtx _ hlx'] at this
  rw [Subgroup.commutator_le]
  intro v hv z hz
  have hlv : ⁅l, v⁆ ∈ Vv (puAmalgam h.le) y := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hC1 (Subgroup.commutator_mem_commutator hv.2 hl))
  have hb' : l * v * l⁻¹ ∈ Vv (puAmalgam h.le) (l • x) := by
    rw [show Vv (puAmalgam h.le) (l • x) = Vi _ (l • x) 2 from rfl, vi_smul]
    exact ⟨v, hv.1, rfl⟩
  have hbz : ⁅l * v * l⁻¹, z⁆ = 1 := by
    have hq : l * v * l⁻¹ ∈ Qv (puAmalgam h.le) (l • x) := vv_le_qv h hb hlx' hb'
    have h1 : ⁅z, l * v * l⁻¹⁆ ∈ ⁅ZM (puAmalgam h.le) (l • x), Qv _ (l • x)⁆ :=
      Subgroup.commutator_mem_commutator hz hq
    rw [commutator_zm_qv _ h20 hlx', Subgroup.mem_bot] at h1
    rw [← commutatorElement_inv, h1, inv_one]
  have e : ⁅v, z⁆ = ⁅l, v⁆⁻¹ * ⁅l * v * l⁻¹, z⁆ * ⁅l, v⁆ * ⁅⁅l, v⁆⁻¹, z⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, hbz, mul_one, inv_mul_cancel, one_mul]
  exact hI (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hlv) (hZV hz))

end Orbit

end CFSG.Quasithin.MS93.S46.QMix
