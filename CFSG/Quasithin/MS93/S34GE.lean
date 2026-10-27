module

public import CFSG.Quasithin.MS93.S34GA
public import CFSG.Quasithin.MS93.S43FFF

public section

namespace CFSG.Quasithin.MS93.S34G

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F
open scoped commutatorElement

section Flat

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hC : CentHyp (puAmalgam h.le))
include h hC

theorem vcirc_le_qv_not_le_gen (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
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
  have hVle := vv_le_vi_sup_commutator_gen h hγ hγε
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

theorem false_of_star_four_flat (hb : 2 < critDist (puAmalgam h.le))
    (hb4 : critDist (puAmalgam h.le) = 4) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α')
    (hBγ : ⁅Vv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2),
      Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)⁆ ≤
        Bloc h.le L (geo (puAmalgam h.le) α' α 2))
    (hVc : ∀ δ ∈ nablaSet h.le L (geo (puAmalgam h.le) α' α 2),
      Vcirc h.le L (geo (puAmalgam h.le) α' α 2) ≤
        conjCl (stab (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)) (ZM (puAmalgam h.le) δ)) :
    False := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = 4 := hs.1.2.1.trans hb4
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = 4 := hc'.2.1.trans hb4
  have hγeq : geo (puAmalgam h.le) α α' 2 = geo (puAmalgam h.le) α' α 2 := by
    rw [← geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist α α' by omega), hd]
  obtain ⟨-, hXα⟩ := vcirc_le_qv_not_le_gen h hC hb hs
  set γ := geo (puAmalgam h.le) α' α 2 with hγdef
  have hγ : IsMVtx (puAmalgam h.le) γ := isMVtx_geo_two _ h20 hb0 hc'
  have hαβ : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α α' 1) :=
    adj_geo_one_of_isCritical _ hb0 hs.1
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α α' 1) γ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := α') (i := 1) (by omega)
    rwa [show (1 + 1 : ℕ) = 2 from rfl, hγeq] at this
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α = 2 := by
    rw [hγdef, dist_geo_right _ (by omega), hd']
  have hdαγ : (puAmalgam h.le).treeGraph.dist α γ = 2 := by rw [tdist_comm]; exact hdγα
  have hQβα : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) ≤ stab _ α :=
    qv_le_stab_of_adj _ hαβ.symm
  have hQβγ : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) ≤ stab _ γ :=
    qv_le_stab_of_adj _ hβγ
  have hZαQγ : ZM (puAmalgam h.le) α ≤ Qv _ γ := zm_le_qv_of_dist_lt _ hα (by omega)
  have hQγβ : Qv (puAmalgam h.le) γ ≤ Qv _ (geo (puAmalgam h.le) α α' 1) :=
    qv_le_qv _ h20 hγ hβγ.symm
  have hαnab : α ∈ nablaSet h.le L γ := by
    refine ⟨hdγα, fun hle => ?_⟩
    rw [zv_of_isMVtx _ hα] at hle
    apply ms22_iv _ h20 hb0 hC hs.1
    rw [hγeq, stab_eq_ltil_sup_qv_gen h hγ hβγ.symm]
    have hN : stab (puAmalgam h.le) α ⊓ stab _ γ ≤ Subgroup.normalizer
        ((ZM (puAmalgam h.le) α ⊔ XM (puAmalgam h.le) γ : Subgroup _) : Set _) :=
      (inf_le_inf (stab_le_normalizer_zm _ α) (stab_le_normalizer_xm _ γ)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    refine sup_le ?_ ((le_inf hQβα hQβγ).trans hN)
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
    · exact ((commutator_bloc_le h hb hγ).trans' (Subgroup.commutator_mono hle le_rfl)).trans
        ((zm_le_xm _ h20 hb0 hγ).trans le_sup_right)
    · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((ltil_le_stab h γ).trans (stab_le_normalizer_xm _ γ))).trans le_sup_right
    · exact (le_inf ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α))
        (hZαQγ.trans (qv_le_stab _ γ))).trans hN
    · exact (le_inf ((xm_le_qv _ γ).trans (hQγβ.trans hQβα))
        ((xm_le_qv _ γ).trans (qv_le_stab _ γ))).trans hN
  obtain ⟨g, hg, hgα⟩ : ∃ g ∈ stab (puAmalgam h.le) γ,
      ¬ (ZM (puAmalgam h.le) α).map (MulAut.conj g).toMonoidHom ≤ Qv _ α := by
    by_contra hcon
    push Not at hcon
    exact hXα ((hVc α hαnab).trans (iSup₂_le fun g hg => hcon g hg))
  have hg' : g ∈ ((Ltil h.le L γ ⊔ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) :
      Subgroup _) : Set _) := stab_eq_ltil_sup_qv_gen h hγ hβγ.symm ▸ hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (hQβγ.trans (stab_le_normalizer_ltil h γ))] at hg'
  obtain ⟨l, hl, t, ht, rfl⟩ := hg'
  have htα : t • α = α := (mem_stab _).mp (hQβα ht)
  have hZl : ZM (puAmalgam h.le) (l • α) = (ZM (puAmalgam h.le) α).map
      (MulAut.conj (l * t)).toMonoidHom := by
    have h1 : (ZM (puAmalgam h.le) α).map (MulAut.conj t).toMonoidHom = ZM _ α := by
      rw [← zm_smul, htα]
    rw [zm_smul, ← map_conj_map_conj, h1]
  set α'' := l • α with hα''
  have hlγ : l • γ = γ := (mem_stab _).mp (ltil_le_stab h γ hl)
  have hZα'' : ¬ ZM (puAmalgam h.le) α'' ≤ Qv _ α := by
    rw [hZl]
    exact hgα
  have hα''M : IsMVtx (puAmalgam h.le) α'' := (isMVtx_smul _ l α).mpr hα
  have hdα''γ : (puAmalgam h.le).treeGraph.dist α'' γ = 2 := by
    rw [hα'', ← hlγ, dist_smul, hdαγ]
  have hdα''α : (puAmalgam h.le).treeGraph.dist α'' α = 4 := by
    have hle := dist_triangle (puAmalgam h.le) α'' γ α
    rw [hdα''γ, hdγα] at hle
    by_contra hne
    exact hZα'' (zm_le_qv_of_dist_lt _ hα''M (by omega))
  have hcrit : IsCritical (puAmalgam h.le) α'' α := ⟨hα''M, hdα''α.trans hb4.symm, hZα''⟩
  have hR := ms22_ii _ h20 hb0 hC (ms22_iii _ h20 hb0 hC hcrit)
  have hVγ : Vv (puAmalgam h.le) α ≤ Qv _ γ := hs.2
  have hZαVγ : ZM (puAmalgam h.le) α ≤ Vv _ γ := by
    rw [← zv_of_isMVtx _ hα]
    exact zv_le_vv h hdγα.le
  have hQZB : ⁅Qv (puAmalgam h.le) γ, ZM (puAmalgam h.le) α⁆ ≤ Bloc h.le L γ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hZαVγ le_rfl).trans hBγ
  have hQZα : ⁅Qv (puAmalgam h.le) γ, ZM (puAmalgam h.le) α⁆ ≤ ZM _ α :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((hQγβ.trans hQβα).trans (stab_le_normalizer_zm _ α))
  have hcomm : ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α''⁆ ≤
      ZM (puAmalgam h.le) α ⊔ ZM (puAmalgam h.le) γ := by
    refine (Subgroup.commutator_mono hVγ le_rfl).trans ?_
    rw [hα'', zm_smul, ← map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ γ
      (ltil_le_stab h γ hl)), ← Subgroup.map_commutator]
    rintro _ ⟨x, hx, rfl⟩
    have hxB := hQZB hx
    have hxl := ((mem_bloc_iff h hb hγ).mp hxB).2 l hl
    have hrw : (MulAut.conj l).toMonoidHom x = ⁅x, l⁆⁻¹ * x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [hrw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hxl))
      (Subgroup.mem_sup_left (hQZα hx))
  have hcen : ZM (puAmalgam h.le) α ⊔ ZM (puAmalgam h.le) γ ≤
      centerOf (Vv (puAmalgam h.le) α) := by
    refine sup_le (le_inf (zm_le_vv h hα) ?_) (le_inf ?_ ?_)
    · exact (zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le (vv_le_qv h hb hα))
    · rw [← zv_of_isMVtx _ hγ]
      exact zv_le_vv h hdαγ.le
    · exact (zm_le_centralizer_qv _ h20 hγ).trans (Subgroup.centralizer_le hVγ)
  have hZβ : ZM (puAmalgam h.le) α'' ≤ Qv _ (geo (puAmalgam h.le) α α' 1) := by
    refine zm_le_qv_of_dist_lt _ hα''M ?_
    have := dist_triangle (puAmalgam h.le) α'' γ (geo (puAmalgam h.le) α α' 1)
    rw [hdα''γ, tdist_comm _ γ, (SimpleGraph.dist_eq_one_iff_adj).mpr hβγ] at this
    omega
  have hcn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (centerOf (Vv (puAmalgam h.le) α) : Set (puAmalgam h.le).Universal) :=
    le_normalizer_inf (stab_le_normalizer_vv h α)
      (le_normalizer_centralizer (stab_le_normalizer_vv h α))
  have hVL := commutator_vv_ltil_le_of_gen h hα hαβ hZβ hZα'' hcn (hcomm.trans hcen)
  have hβH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  have hVi := vi_one_comm_eq_bot h hb hβH
  have hVle := (vv_le_vi_sup_commutator_gen h hα hαβ).trans (sup_le_sup_left hVL _)
  have hViV : Vi (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) 1 ≤ Vv _ α := by
    refine iSup₂_le fun ρ hρ => zv_le_vv h ?_
    have := dist_triangle (puAmalgam h.le) α (geo (puAmalgam h.le) α α' 1) ρ
    rw [(SimpleGraph.dist_eq_one_iff_adj).mpr hαβ] at this
    have hρ1 : (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) α α' 1) ρ ≤ 1 := hρ
    omega
  have hab : ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hsup : Vi (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) 1 ⊔
        centerOf (Vv (puAmalgam h.le) α) ≤ Subgroup.centralizer
          ((Vi (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) 1 ⊔
            centerOf (Vv (puAmalgam h.le) α) : Subgroup _) : Set _) := by
      have hc1 : centerOf (Vv (puAmalgam h.le) α) ≤ Subgroup.centralizer
          ((Vi (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) 1 ⊔
            centerOf (Vv (puAmalgam h.le) α) : Subgroup _) : Set _) :=
        inf_le_right.trans (Subgroup.centralizer_le (sup_le hViV inf_le_left))
      refine sup_le ?_ hc1
      rw [Subgroup.le_centralizer_iff]
      refine sup_le ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hVi) ?_
      exact inf_le_right.trans (Subgroup.centralizer_le hViV)
    exact hVle.trans (hsup.trans (Subgroup.centralizer_le hVle))
  obtain ⟨x, hx⟩ := exists_smul_eq_of_isMVtx _ hα hγ
  have habγ : ⁅Vv (puAmalgam h.le) γ, Vv (puAmalgam h.le) γ⁆ = ⊥ := by
    rw [← hx, show Vv (puAmalgam h.le) (x • α) = (Vv (puAmalgam h.le) α).map
      (MulAut.conj x).toMonoidHom from vi_smul _ x α 2, ← Subgroup.map_commutator, hab,
      Subgroup.map_bot]
  have hZα''V : ZM (puAmalgam h.le) α'' ≤ Vv _ γ := by
    rw [← zv_of_isMVtx _ hα''M]
    exact zv_le_vv h (by rw [tdist_comm]; exact hdα''γ.le)
  apply hR
  rw [eq_bot_iff, ← habγ]
  exact Subgroup.commutator_mono hZαVγ hZα''V

end Flat

section Props

@[expose] def S43b4Flat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    IsSL3U M T L → CentHyp (puAmalgam h.le) → critDist (puAmalgam h.le) = 4 →
    ∀ α α' : Vtx (puAmalgam h.le), ¬ S4A.Star (puAmalgam h.le) α α'

theorem s43b4Flat_of (h14 : MS14AS) (hSQ : SQTKQuot) : S43b4Flat := by
  intro G _ _ M T L h hU hC hb4 α α' hs
  obtain ⟨n, F, _, _, φ, hcard, hφs, hφ⟩ := exists_natural_flat h hU
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hγ := isMVtx_geo_two _ h20 hb0 hc'
  obtain ⟨γ', hsγ⟩ := exists_star_at _ hs hγ
  have hcγ := S43F.isC1Flat_of_crit h14 hSQ h hU hC hcard hφs hφ hb
    (ms22_iii _ h20 hb0 hC hsγ.1) (vv_comm_le_zm_of_star_flat h hU hC hcard hφs hφ hb hsγ)
    (relIndex_critR0_sup_zm_le_flat h hU hC hcard hφs hφ hb hsγ)
  exact false_of_star_four_flat h hC hb hb4 hs (S43F.isC1Flat_bloc h hb hγ hcγ).1
    fun δ hδ => S43F.vcirc_le_conjCl_flat h hb hγ hcγ hδ

end Props

end CFSG.Quasithin.MS93.S34G
