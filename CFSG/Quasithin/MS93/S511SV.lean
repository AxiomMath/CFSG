module

public import CFSG.Quasithin.MS93.S38EBase
public import CFSG.Quasithin.MS93.S510Ctr

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S511S

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem vv_le_qv_of_dist (h : PUHyp M T L) {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hd : (puAmalgam h.le).treeGraph.dist δ ρ + 2 < critDist (puAmalgam h.le)) :
    Vv _ δ ≤ Qv _ ρ := by
  refine iSup₂_le fun ρ' hρ' => ?_
  obtain ⟨γ, hγ, hdγ, hle⟩ := S38E.exists_zv_le_zm _ hδ hρ'
  refine hle.trans (zm_le_qv_of_dist_lt _ hγ ?_)
  have := dist_triangle _ γ δ ρ
  rw [tdist_comm _ γ δ] at this
  omega

theorem vv_le_centralizer_zm (h : PUHyp M T L) {δ γ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hγ : IsMVtx _ γ)
    (hd : (puAmalgam h.le).treeGraph.dist δ γ + 2 < critDist (puAmalgam h.le)) :
    Vv _ δ ≤ Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  refine iSup₂_le fun ρ' hρ' => ?_
  obtain ⟨γ', hγ', hdγ', hle⟩ := S38E.exists_zv_le_zm _ hδ hρ'
  refine hle.trans (S510.zm_le_centralizer_zm_of_dist hyp hb0 hγ' hγ ?_)
  have := dist_triangle _ γ' δ γ
  rw [tdist_comm _ γ' δ] at this
  omega

theorem vv_le_centralizer_vv (h : PUHyp M T L) {δ δ' : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδ' : IsMVtx _ δ')
    (hd : (puAmalgam h.le).treeGraph.dist δ δ' + 4 < critDist (puAmalgam h.le)) :
    Vv _ δ ≤ Subgroup.centralizer (Vv _ δ' : Set (puAmalgam h.le).Universal) := by
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun ρ' hρ' => ?_
  obtain ⟨γ, hγ, hdγ, hle⟩ := S38E.exists_zv_le_zm _ hδ' hρ'
  refine hle.trans ?_
  rw [← Subgroup.le_centralizer_iff]
  refine vv_le_centralizer_zm h hδ hγ ?_
  have := dist_triangle _ δ δ' γ
  omega

theorem vv_le_centralizer_self (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    Vv _ δ ≤ Subgroup.centralizer (Vv _ δ : Set (puAmalgam h.le).Universal) :=
  vv_le_centralizer_vv h hδ hδ (by simp; omega)

theorem isPGroup_vv (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    IsPGroup 2 ↥(Vv _ δ) ∧ Finite ↥(Vv _ δ) := by
  have hyp := h.hyp20
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  have hadj : (puAmalgam h.le).treeGraph.Adj (g • baseA (puAmalgam h.le)) (g • baseB _) :=
    (adj_smul _ g _ _).2 (adj_baseA_baseB _)
  have hle : Vv _ (g • baseA (puAmalgam h.le)) ≤ Qv _ (g • baseB (puAmalgam h.le)) :=
    (S38E.vv_le_qv _ hb hδ).trans (qv_le_qv _ hyp hδ hadj)
  have hεM : ¬ IsMVtx _ (g • baseB (puAmalgam h.le)) := (isMVtx_iff_of_adj _ hadj).1 hδ
  have : Finite ↥(Qv (puAmalgam h.le) (g • baseB (puAmalgam h.le))) := finite_qv _ hyp hεM
  exact ⟨(isPGroup_qv _ hyp hεM).to_le hle,
    Finite.of_injective _ (Subgroup.inclusion_injective hle)⟩

end S511S

end CFSG.Quasithin.MS93
