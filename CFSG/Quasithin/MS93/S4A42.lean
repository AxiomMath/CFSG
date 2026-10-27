module

public import CFSG.Quasithin.MS93.S4AVtx

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section S42ii

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

omit hfull in
theorem zv_le_vv {α ρ : Vtx (puAmalgam h.le)} (hd : (puAmalgam h.le).treeGraph.dist α ρ ≤ 2) :
    Zv (puAmalgam h.le) ρ ≤ Vv _ α :=
  le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
    (puAmalgam h.le).treeGraph.dist α ρ ≤ 2}) => Zv (puAmalgam h.le) ρ) ρ hd le_rfl

theorem commutator_zm_le_dloc (hb : 2 < critDist (puAmalgam h.le))
    {α δ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hδ : IsMVtx _ δ)
    (hd : (puAmalgam h.le).treeGraph.dist α δ = 2) {Y : Subgroup (puAmalgam h.le).Universal}
    (hYn : stab _ α ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal))
    (hYQ : Y ≤ Qv _ α) (hVY : ⁅Vcirc h.le L α, Y⁆ ≤ Dloc h.le L α) :
    ⁅ZM (puAmalgam h.le) δ, Y⁆ ≤ Dloc h.le L α := by
  have h20 := h.hyp20
  have hQαs : Qv (puAmalgam h.le) α ≤ stab _ α := qv_le_stab _ α
  have hDn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Dloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α
  have hLs : Ltil h.le L α ≤ stab _ α := ltil_le_stab h α
  have hDQ : Dloc h.le L α ≤ Qv _ α := by
    rw [Dloc, h.puTrans_Dq hα]
    exact inf_le_left
  have hDc : Dloc h.le L α ≤
      Subgroup.centralizer (Ltil h.le L α : Set (puAmalgam h.le).Universal) := by
    rw [Dloc, h.puTrans_Dq hα]
    exact inf_le_right
  have hZQ : ZM (puAmalgam h.le) δ ≤ Qv _ α :=
    zm_le_qv_of_dist_lt _ hδ (by rw [tdist_comm]; omega)
  have hQαδ : Qv (puAmalgam h.le) α ≤ stab _ δ := qv_le_stab_of_dist_le_two _ h20 hα hd.le
  have hQδα : Qv (puAmalgam h.le) δ ≤ stab _ α :=
    qv_le_stab_of_dist_le_two _ h20 hδ (by rw [tdist_comm]; omega)
  have hZY : ⁅ZM (puAmalgam h.le) δ, Y⁆ ≤ ZM _ δ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hYQ.trans hQαδ).trans (stab_le_normalizer_zm _ δ))
  set K := ⁅ZM (puAmalgam h.le) δ, Y⁆ ⊔ Dloc h.le L α with hK
  have hKQ : K ≤ Qv _ α := sup_le (hZY.trans hZQ) hDQ
  have hKs : K ≤ stab _ α := hKQ.trans hQαs
  have hLK : Ltil h.le L α ≤ Subgroup.normalizer (K : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun l hl => ?_
    rw [hK, Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hDn (hLs hl))]
    refine sup_le ?_ le_sup_right
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hYn (hLs hl)),
      Subgroup.commutator_le]
    rintro _ ⟨z, hz, rfl⟩ y hy
    have hzV : z⁻¹ ∈ Vv (puAmalgam h.le) α := by
      have hz' : z ∈ Zv (puAmalgam h.le) δ := by
        rw [zv_of_isMVtx _ hδ]
        exact hz
      exact Subgroup.inv_mem _ (zv_le_vv h hd.le hz')
    have hvV : ⁅z⁻¹, l⁆ ∈ Vcirc h.le L α := Subgroup.commutator_mem_commutator hzV hl
    have hrw : ⁅(MulAut.conj l).toMonoidHom z, y⁆ = z * ⁅⁅z⁻¹, l⁆, y⁆ * z⁻¹ * ⁅z, y⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def, inv_inv]
      group
    rw [hrw]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_)
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hz hy))
    exact (Subgroup.mem_normalizer_iff.mp (hDn (hQαs (hZQ hz))) _).mp
      (hVY (Subgroup.commutator_mem_commutator hvV hy))
  have hKQδ : ⁅K, Qv (puAmalgam h.le) δ⁆ ≤ Dloc h.le L α := by
    refine S4A.commutator_sup_le_of ?_ ?_ (((hZY.trans hZQ).trans hQαs).trans hDn)
      ((hDQ.trans hQαs).trans hDn)
    · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (hZY.trans (zm_le_centralizer_qv _ h20 hδ))]
      exact bot_le
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQδα.trans hDn)
  have hJK : ⁅⁅Ltil h.le L α, Qv (puAmalgam h.le) δ⁆, K⁆ ≤ Dloc h.le L α := by
    refine three_subgroups_le (hLs.trans hDn) (hQδα.trans hDn) (hKs.trans hDn) ?_ ?_
    · have : ⁅Qv (puAmalgam h.le) δ, K⁆ ≤ Dloc h.le L α := by
        rw [Subgroup.commutator_comm]
        exact hKQδ
      refine (Subgroup.commutator_mono this le_rfl).trans ?_
      rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hDc]
      exact bot_le
    · exact (Subgroup.commutator_mono
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hLK) le_rfl).trans hKQδ
  have hJL : ⁅Ltil h.le L α, Qv (puAmalgam h.le) δ⁆ ≤ Ltil h.le L α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQδα.trans (stab_le_normalizer_ltil h α))
  rcases commutator_ltil_le_or h hα hJL (Subgroup.normalizer_commutator_ge_left _ _) with hc | hc
  ·
    have hO : pCoreLtil h α ≤ Qv _ α := pCoreLtil_le_qv h hα
    have hQn : stab (puAmalgam h.le) α ≤
        Subgroup.normalizer (Qv (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
      stab_le_normalizer_qv _ α
    have h3 : ⁅⁅Ltil h.le L α, Ltil h.le L α⁆, Qv (puAmalgam h.le) δ⁆ ≤ Qv _ α := by
      refine three_subgroups_le (hLs.trans hQn) (hLs.trans hQn) (hQδα.trans hQn) (hc.trans hO) ?_
      rw [Subgroup.commutator_comm (Qv (puAmalgam h.le) δ) (Ltil h.le L α)]
      exact hc.trans hO
    rw [ltil_perfect h hα] at h3
    have hαρ : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α δ 1) :=
      adj_geo_one _ (by omega)
    have hρδ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α δ 1) δ := by
      have := adj_geo (puAmalgam h.le) (u := α) (w := δ) (i := 1) (by omega)
      rwa [show geo (puAmalgam h.le) α δ (1 + 1) = δ from geo_of_le _ (by omega)] at this
    have hle : Qv (puAmalgam h.le) δ ≤ Qv _ α := by
      refine le_qv_of_commutator_le h hfull hα hαρ (qv_le_qv _ h20 hδ hρδ.symm) ?_
      rw [Subgroup.commutator_comm]
      exact h3
    have heq := qv_eq_of_le h hα hδ hle
    have hZeq : ZM (puAmalgam h.le) δ = ZM _ α := by
      rw [← xm_eq_zm h hfull hδ, ← xm_eq_zm h hfull hα, XM, XM, heq]
    rw [hZeq, (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le hYQ))]
    exact bot_le
  ·
    have hKL : ⁅K, Ltil h.le L α⁆ ≤ Dloc h.le L α := by
      refine (Subgroup.commutator_mono le_rfl hc).trans ?_
      rw [Subgroup.commutator_comm]
      exact hJK
    exact le_sup_left.trans (le_dloc_of_commutator_le h hα hKQ hKL)

theorem commutator_vv_le_dloc (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {Y : Subgroup (puAmalgam h.le).Universal}
    (hYn : stab _ α ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal))
    (hYQ : Y ≤ Qv _ α) (hVY : ⁅Vcirc h.le L α, Y⁆ ≤ Dloc h.le L α) :
    ⁅Vv (puAmalgam h.le) α, Y⁆ ≤ Dloc h.le L α := by
  have h20 := h.hyp20
  have hDn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Dloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α
  have hV : Vv (puAmalgam h.le) α =
      ⨆ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
        Zv (puAmalgam h.le) ρ := by
    rw [show Vv (puAmalgam h.le) α = Vi (puAmalgam h.le) α 2 from rfl]
    unfold Vi
    exact iSup_subtype'
  have hZY : ⁅ZM (puAmalgam h.le) α, Y⁆ ≤ Dloc h.le L α := by
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le hYQ))]
    exact bot_le
  have hVn : (⨆ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
      Zv (puAmalgam h.le) ρ) ≤
        Subgroup.normalizer (Dloc h.le L α : Set (puAmalgam h.le).Universal) := by
    rw [← hV]
    exact ((vv_le_qv h hb hα).trans (qv_le_stab _ α)).trans hDn
  rw [hV]
  refine commutator_iSup_le_of (fun ρ => ?_) hVn
  obtain ⟨ρ, hρ⟩ := ρ
  rcases isMVtx_of_dist_le_two h hα hρ with hρM | hadj
  · rw [zv_of_isMVtx _ hρM]
    rcases Nat.lt_or_ge ((puAmalgam h.le).treeGraph.dist α ρ) 1 with h0 | h1
    · have : ρ = α := ((dist_eq_zero_iff (puAmalgam h.le)).mp (Nat.lt_one_iff.mp h0)).symm
      subst this
      exact hZY
    · have hev : Even ((puAmalgam h.le).treeGraph.dist α ρ) :=
        (even_dist_iff (puAmalgam h.le) α ρ).mpr ⟨fun _ => hρM, fun _ => hα⟩
      obtain ⟨k, hk⟩ := hev
      have hd : (puAmalgam h.le).treeGraph.dist α ρ = 2 := by
        show (puAmalgam h.le).treeGraph.dist α ρ = 2
        omega
      exact commutator_zm_le_dloc h hfull hb hα hρM hd hYn hYQ hVY
  · have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by
      rw [← isMVtx_iff_of_adj (puAmalgam h.le) hadj]
      exact hα
    rw [zv_of_not_isMVtx _ hρH]
    exact (Subgroup.commutator_mono (zh_le_zm _ hadj) le_rfl).trans hZY

end S42ii

end CFSG.Quasithin.MS93.S4A
