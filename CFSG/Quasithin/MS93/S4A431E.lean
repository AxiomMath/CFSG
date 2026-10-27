module

public import CFSG.Quasithin.MS93.S4A431D

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Dist

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem vv_le_qv_of_dist {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hd : (puAmalgam h.le).treeGraph.dist δ ρ + 2 < critDist (puAmalgam h.le)) :
    Vv (puAmalgam h.le) δ ≤ Qv _ ρ := by
  refine iSup₂_le fun μ hμ => ?_
  have hμ' : (puAmalgam h.le).treeGraph.dist δ μ ≤ 2 := hμ
  rcases isMVtx_of_dist_le_two h hδ hμ' with hμM | hadj
  · rw [zv_of_isMVtx _ hμM]
    refine zm_le_qv_of_dist_lt _ hμM ?_
    have := dist_triangle (puAmalgam h.le) μ δ ρ
    rw [tdist_comm _ μ δ] at this
    omega
  · have hμH : ¬ IsMVtx (puAmalgam h.le) μ := by
      rw [← isMVtx_iff_of_adj _ hadj]
      exact hδ
    rw [zv_of_not_isMVtx _ hμH]
    exact (zh_le_zm _ hadj).trans (zm_le_qv_of_dist_lt _ hδ (by omega))

theorem vi_one_le_qv_of_dist {β ρ : Vtx (puAmalgam h.le)} (hβ : ¬ IsMVtx (puAmalgam h.le) β)
    (hd : (puAmalgam h.le).treeGraph.dist β ρ + 1 < critDist (puAmalgam h.le)) :
    Vi (puAmalgam h.le) β 1 ≤ Qv _ ρ := by
  refine iSup₂_le fun μ hμ => ?_
  have hμ' : (puAmalgam h.le).treeGraph.dist β μ ≤ 1 := hμ
  by_cases hμM : IsMVtx (puAmalgam h.le) μ
  · rw [zv_of_isMVtx _ hμM]
    refine zm_le_qv_of_dist_lt _ hμM ?_
    have := dist_triangle (puAmalgam h.le) μ β ρ
    rw [tdist_comm _ μ β] at this
    omega
  · have hμβ : μ = β := by
      by_contra hne
      have hadj : (puAmalgam h.le).treeGraph.Adj β μ := by
        rcases (dist_le_one_iff (puAmalgam h.le)).mp hμ' with h0 | ha
        · exact absurd h0 hne
        · exact ha
      exact hβ ((isMVtx_iff_of_adj _ hadj).mpr hμM)
    subst hμβ
    rw [zv_of_not_isMVtx _ hμM]
    obtain ⟨δ, hδ⟩ := exists_adj (puAmalgam h.le) μ
    have hδM : IsMVtx (puAmalgam h.le) δ := by
      by_contra hδM
      exact hμM ((isMVtx_iff_of_adj _ hδ).mpr hδM)
    refine (zh_le_zm _ hδ.symm).trans (zm_le_qv_of_dist_lt _ hδM ?_)
    have h1 := dist_triangle (puAmalgam h.le) δ μ ρ
    rw [tdist_comm _ δ μ, (SimpleGraph.dist_eq_one_iff_adj).mpr hδ] at h1
    omega

end Dist

section VI

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem vcirc_le_qv_not_le (hC : CentHyp (puAmalgam h.le))
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α') :
    Vcirc h.le L (geo (puAmalgam h.le) α' α 2) ≤ Qv _ (geo (puAmalgam h.le) α α' 1) ∧
      ¬ Vcirc h.le L (geo (puAmalgam h.le) α' α 2) ≤ Qv _ α := by
  obtain ⟨hc, -⟩ := hs
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := hc'.2.1
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  have hVn := stab_le_normalizer_vv h (geo (puAmalgam h.le) α' α 2)
  have hVcV : Vcirc h.le L (geo (puAmalgam h.le) α' α 2) ≤
      Vv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h _).trans hVn)
  have hdγβ : (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) α' α 2)
      (geo (puAmalgam h.le) α α' 1) = critDist (puAmalgam h.le) - 3 := by
    rw [← geo_symm _ (show 1 ≤ (puAmalgam h.le).treeGraph.dist α α' by omega),
      dist_geo_geo _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist α α' - 1 by omega) (by omega),
      hd]
    omega
  have hdγα : (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) α' α 2) α =
      critDist (puAmalgam h.le) - 2 := by
    rw [dist_geo_right _ (by omega), hd']
  refine ⟨hVcV.trans (vv_le_qv_of_dist h hγ (by omega)), fun hle => ?_⟩
  have hγε : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 2)
      (geo (puAmalgam h.le) α' α 3) := adj_geo _ (i := 2) (by omega)
  have hVle := vv_le_vi_sup_commutator h hfull hγ hγε
  have hεα : (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) α' α 3) α =
      critDist (puAmalgam h.le) - 3 := by
    rw [dist_geo_right _ (by omega), hd']
  have hεH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 3) := by
    rw [← isMVtx_iff_of_adj _ hγε]
    exact hγ
  have hVi : Vi (puAmalgam h.le) (geo (puAmalgam h.le) α' α 3) 1 ≤ Qv _ α :=
    vi_one_le_qv_of_dist h hεH (by omega)
  have hVγα : Vv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) ≤ Qv _ α :=
    hVle.trans (sup_le hVi hle)
  apply hc'.2.2
  rw [← zv_of_isMVtx _ hc'.1]
  refine (zv_le_vv h ?_).trans hVγα
  rw [tdist_comm, dist_geo _ (by omega)]

theorem concl431_vi (hC : CentHyp (puAmalgam h.le)) (hb : 2 < critDist (puAmalgam h.le))
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    (hc : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)) :
    Fintype.card F ^ 2 ≤
        Nat.card ↥⁅Vv (puAmalgam h.le) α, Vcirc h.le L (geo (puAmalgam h.le) α' α 2)⁆ ∧
      Fintype.card F ^ 2 ≤ Nat.card ↥(Hloc h.le L α) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) :=
    isMVtx_geo_two _ h20 hb0 hc'
  obtain ⟨hXβ, hXα⟩ := vcirc_le_qv_not_le h hfull hC hb hs
  have h1 := sq_le_card_commutator_vv h hfull hC hb hα (adj_geo_one_of_isCritical _ hb0 hs.1) hφ
    hc hXβ hXα
  refine ⟨h1, h1.trans ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hα hγ
  have hH : Nat.card ↥(Hloc h.le L (geo (puAmalgam h.le) α' α 2)) =
      Nat.card ↥(Hloc h.le L α) := by
    rw [← hg, hloc_smul h, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [← hH]
  have hle : ⁅Vv (puAmalgam h.le) α, Vcirc h.le L (geo (puAmalgam h.le) α' α 2)⁆ ≤
      Hloc h.le L (geo (puAmalgam h.le) α' α 2) := by
    rw [Hloc, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hs.2
  have hfin : Finite ↥(Hloc h.le L (geo (puAmalgam h.le) α' α 2)) := by
    have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := hc'.2.1
    have h1γ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
        (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by omega)
    have h1H : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
      rw [isMVtx_iff_of_adj _ h1γ]
      exact fun hh => hh hγ
    have hHQ : Hloc h.le L (geo (puAmalgam h.le) α' α 2) ≤ Qv _ (geo (puAmalgam h.le) α' α 1) := by
      rw [Hloc]
      refine (commutator_le_of_le ((Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((ltil_le_stab h _).trans (stab_le_normalizer_vv h _))).trans (vv_le_qv h hb hγ))
          le_rfl).trans ?_
      exact qv_le_qv _ h20 hγ h1γ.symm
    have := finite_qv _ h20 h1H
    exact Finite.of_injective _ (Subgroup.inclusion_injective hHQ)
  exact Subgroup.card_le_of_le hle

omit hfull in
theorem commutator_zm_qv_eq_usup_smul {δ ρ : Vtx (puAmalgam h.le)} (g : (puAmalgam h.le).Universal)
    (hE : ⁅ZM (puAmalgam h.le) ρ, Qv (puAmalgam h.le) δ⁆ =
      Usup (puAmalgam h.le) ρ (geo (puAmalgam h.le) δ ρ 1)) :
    ⁅ZM (puAmalgam h.le) (g • ρ), Qv (puAmalgam h.le) (g • δ)⁆ =
      Usup (puAmalgam h.le) (g • ρ) (geo (puAmalgam h.le) (g • δ) (g • ρ) 1) := by
  rw [zm_smul, qv_smul, ← Subgroup.map_commutator, hE, geo_smul, usup_smul]

theorem concl431_vii_at (hC : CentHyp (puAmalgam h.le)) (hb : 2 < critDist (puAmalgam h.le))
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    (hcα : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    (hcγ : IsC1 h.le L (Fintype.card F) (geo (puAmalgam h.le) α' α 2)
      (Vv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2))
      (ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)))
    {ρ : Vtx (puAmalgam h.le)} (hρ : ρ ∈ nablaSet h.le L (geo (puAmalgam h.le) α' α 2)) :
    ⁅ZM (puAmalgam h.le) ρ, Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)⁆ =
      Usup (puAmalgam h.le) ρ (geo (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) ρ 1) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hs.1.2.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := hc'.2.1
  set γ := geo (puAmalgam h.le) α' α 2 with hγdef
  have hγ : IsMVtx (puAmalgam h.le) γ := isMVtx_geo_two _ h20 hb0 hc'
  obtain ⟨-, hXα⟩ := vcirc_le_qv_not_le h hfull hC hb hs
  obtain ⟨g, hg, hgρ⟩ : ∃ g ∈ stab (puAmalgam h.le) γ,
      ¬ (ZM (puAmalgam h.le) ρ).map (MulAut.conj g).toMonoidHom ≤ Qv _ α := by
    by_contra hcon
    push Not at hcon
    exact hXα ((vcirc_le_conjCl h hfull hb hγ hcγ hρ).trans (iSup₂_le fun g hg => hcon g hg))
  have hgγ : g • γ = γ := (mem_stab _).mp hg
  suffices key : ⁅ZM (puAmalgam h.le) (g • ρ), Qv (puAmalgam h.le) γ⁆ =
      Usup (puAmalgam h.le) (g • ρ) (geo (puAmalgam h.le) γ (g • ρ) 1) by
    have hginv : g⁻¹ • γ = γ := by rw [inv_smul_eq_iff, hgγ]
    have := commutator_zm_qv_eq_usup_smul h g⁻¹ (δ := γ) (ρ := g • ρ) key
    rwa [inv_smul_smul, hginv] at this
  have hρ' : g • ρ ∈ nablaSet h.le L γ := by
    rw [← hgγ]
    exact (mem_nablaSet_smul h g γ ρ).mpr hρ
  obtain ⟨hdρ', -⟩ := hρ'
  have hρ'M : IsMVtx (puAmalgam h.le) (g • ρ) := by
    have hev : Even ((puAmalgam h.le).treeGraph.dist γ (g • ρ)) := ⟨1, by rw [hdρ']⟩
    exact ((even_dist_iff (puAmalgam h.le) γ (g • ρ)).mp hev).1 hγ
  have hZρ' : ¬ ZM (puAmalgam h.le) (g • ρ) ≤ Qv _ α := by
    rw [zm_smul]
    exact hgρ
  have hdγβ : (puAmalgam h.le).treeGraph.dist γ (geo (puAmalgam h.le) α α' 1) =
      critDist (puAmalgam h.le) - 3 := by
    rw [hγdef, ← geo_symm _ (show 1 ≤ (puAmalgam h.le).treeGraph.dist α α' by omega),
      dist_geo_geo _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist α α' - 1 by omega) (by omega),
      hd]
    omega
  have hZβ : ZM (puAmalgam h.le) (g • ρ) ≤ Qv _ (geo (puAmalgam h.le) α α' 1) := by
    refine zm_le_qv_of_dist_lt _ hρ'M ?_
    have := dist_triangle (puAmalgam h.le) (g • ρ) γ (geo (puAmalgam h.le) α α' 1)
    rw [tdist_comm _ (g • ρ) γ, hdρ', hdγβ] at this
    have hb6 : 4 ≤ critDist (puAmalgam h.le) := by
      have := two_le_critDist _ h20 hb0
      obtain ⟨k, hk⟩ := ms21_v _ h20
      omega
    omega
  have hq2 := sq_le_card_commutator_vv h hfull hC hb hα (adj_geo_one_of_isCritical _ hb0 hs.1)
    hφ hcα hZβ hZρ'
  have hγμ : (puAmalgam h.le).treeGraph.Adj γ (geo (puAmalgam h.le) γ (g • ρ) 1) :=
    adj_geo_one _ (by omega)
  have hμρ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) γ (g • ρ) 1) (g • ρ) := by
    have := adj_geo (puAmalgam h.le) (u := γ) (w := g • ρ) (i := 1) (by omega)
    rwa [show geo (puAmalgam h.le) γ (g • ρ) (1 + 1) = g • ρ from geo_of_le _ (by omega)] at this
  have hμH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) γ (g • ρ) 1) := by
    rw [← isMVtx_iff_of_adj _ hγμ]
    exact hγ
  have hle1 : ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) (g • ρ)⁆ ≤
      ⁅ZM (puAmalgam h.le) (g • ρ), Qv (puAmalgam h.le) γ⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hs.2
  have hle2 : ⁅ZM (puAmalgam h.le) (g • ρ), Qv (puAmalgam h.le) γ⁆ ≤
      Usup (puAmalgam h.le) (g • ρ) (geo (puAmalgam h.le) γ (g • ρ) 1) := by
    rw [Usup, zv_of_isMVtx _ hρ'M]
    exact Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hγ hγμ)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hρ'M
  have hβs : Qv (puAmalgam h.le) (geo (puAmalgam h.le) γ (g • ρ) 1) ≤ stab _ (g • ρ) :=
    qv_le_stab_of_adj _ hμρ
  have hUcard : Nat.card ↥(Usup (puAmalgam h.le) (g • ρ) (geo (puAmalgam h.le) γ (g • ρ) 1)) ≤
      Fintype.card F ^ 2 := by
    obtain ⟨n, hn⟩ := hφ.1
    have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
    have : CharP F 2 := FFC.charP_two_of_card_pow hFn
    rw [usup_eq_commutator_uloc h hfull hρ'M hμρ.symm, card_commutator_eq hψ hβs,
      ← Nat.card_eq_fintype_card]
    have hT : IsPGroup 2 ↥((Qv (puAmalgam h.le) (geo (puAmalgam h.le) γ (g • ρ) 1)).subgroupOf
        (stab (puAmalgam h.le) (g • ρ))) :=
      (isPGroup_qv _ h20 hμH).of_equiv (Subgroup.subgroupOfEquivOfLe hβs).symm
    exact card_commN_le_sq (hT.map _)
  have hfinU : Finite ↥(Usup (puAmalgam h.le) (g • ρ) (geo (puAmalgam h.le) γ (g • ρ) 1)) := by
    have hUQ : Usup (puAmalgam h.le) (g • ρ) (geo (puAmalgam h.le) γ (g • ρ) 1) ≤
        Qv _ (geo (puAmalgam h.le) γ (g • ρ) 1) := by
      rw [Usup, zv_of_isMVtx _ hρ'M]
      exact commutator_le_of_le ((zm_le_qv_self _ hρ'M hb0).trans
        (qv_le_qv _ h20 hρ'M hμρ.symm)) le_rfl
    have := finite_qv _ h20 hμH
    exact Finite.of_injective _ (Subgroup.inclusion_injective hUQ)
  have hfinC : Finite ↥⁅ZM (puAmalgam h.le) (g • ρ), Qv (puAmalgam h.le) γ⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective hle2)
  refine Subgroup.eq_of_le_of_card_ge hle2 ?_
  exact hUcard.trans (hq2.trans (Subgroup.card_le_of_le hle1))

theorem concl431_vii (hC : CentHyp (puAmalgam h.le)) (hb : 2 < critDist (puAmalgam h.le))
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α')
    (hcα : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    (hcγ : IsC1 h.le L (Fintype.card F) (geo (puAmalgam h.le) α' α 2)
      (Vv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2))
      (ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)))
    {δ : Vtx (puAmalgam h.le)} (hδ : δ ∈ nablaSet h.le L α) :
    ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ =
      Usup (puAmalgam h.le) δ (geo (puAmalgam h.le) α δ 1) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  obtain ⟨x, hx⟩ := exists_smul_eq_of_isMVtx _ hγ hs.1.1
  have hδ' : x⁻¹ • δ ∈ nablaSet h.le L (geo (puAmalgam h.le) α' α 2) := by
    rw [← (mem_nablaSet_smul h x _ (x⁻¹ • δ)), smul_inv_smul, hx]
    exact hδ
  have := commutator_zm_qv_eq_usup_smul h x
    (concl431_vii_at h hfull hC hb hφ hs hcα hcγ hδ')
  rwa [smul_inv_smul, hx] at this

end VI

end CFSG.Quasithin.MS93.S4A
