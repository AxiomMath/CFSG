module

public import CFSG.Quasithin.MS93.S4A431E

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Index

variable {G : Type*} [Group G]

theorem relIndex_sup_of_le_normalizer {H N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

end Index

section Abelian

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem exists_zv_le_zm {α ρ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hρ : (puAmalgam h.le).treeGraph.dist α ρ ≤ 2) :
    ∃ μ, IsMVtx (puAmalgam h.le) μ ∧ (puAmalgam h.le).treeGraph.dist α μ ≤ 2 ∧
      Zv (puAmalgam h.le) ρ ≤ ZM (puAmalgam h.le) μ := by
  rcases isMVtx_of_dist_le_two h hα hρ with hρM | hadj
  · exact ⟨ρ, hρM, hρ, (zv_of_isMVtx _ hρM).le⟩
  · have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by
      rw [← isMVtx_iff_of_adj _ hadj]
      exact hα
    refine ⟨α, hα, by simp, ?_⟩
    rw [zv_of_not_isMVtx _ hρH]
    exact zh_le_zm _ hadj

theorem zm_le_centralizer_zm {μ μ' : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμ' : IsMVtx _ μ')
    (hd : (puAmalgam h.le).treeGraph.dist μ μ' < critDist (puAmalgam h.le)) :
    ZM (puAmalgam h.le) μ ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) μ' : Set (puAmalgam h.le).Universal) := by
  rw [Subgroup.le_centralizer_iff]
  exact (zm_le_centralizer_qv _ h.hyp20 hμ').trans
    (Subgroup.centralizer_le (zm_le_qv_of_dist_lt _ hμ hd))

theorem vv_comm_eq_bot (hb : 4 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) : ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨μ, hμ, hdμ, hρμ⟩ := exists_zv_le_zm h hα hρ
  refine hρμ.trans ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun ρ' hρ' => ?_
  obtain ⟨μ', hμ', hdμ', hρμ'⟩ := exists_zv_le_zm h hα hρ'
  refine hρμ'.trans (zm_le_centralizer_zm h hμ' hμ ?_)
  have := dist_triangle (puAmalgam h.le) μ' α μ
  rw [tdist_comm _ μ' α] at this
  omega

theorem vi_one_comm_eq_bot (hb : 2 < critDist (puAmalgam h.le)) {β : Vtx (puAmalgam h.le)}
    (hβ : ¬ IsMVtx (puAmalgam h.le) β) :
    ⁅Vi (puAmalgam h.le) β 1, Vi (puAmalgam h.le) β 1⁆ = ⊥ := by
  have hgen : ∀ ρ, (puAmalgam h.le).treeGraph.dist β ρ ≤ 1 → ∃ δ,
      IsMVtx (puAmalgam h.le) δ ∧ (puAmalgam h.le).treeGraph.dist β δ ≤ 1 ∧
        Zv (puAmalgam h.le) ρ ≤ ZM (puAmalgam h.le) δ := by
    intro ρ hρ
    by_cases hρM : IsMVtx (puAmalgam h.le) ρ
    · exact ⟨ρ, hρM, hρ, (zv_of_isMVtx _ hρM).le⟩
    · have hρβ : ρ = β := by
        by_contra hne
        rcases (dist_le_one_iff (puAmalgam h.le)).mp hρ with h0 | ha
        · exact hne h0
        · exact hβ ((isMVtx_iff_of_adj _ ha).mpr hρM)
      subst hρβ
      obtain ⟨δ, hδ⟩ := exists_adj (puAmalgam h.le) ρ
      have hδM : IsMVtx (puAmalgam h.le) δ := by
        by_contra hδM
        exact hρM ((isMVtx_iff_of_adj _ hδ).mpr hδM)
      refine ⟨δ, hδM, ((SimpleGraph.dist_eq_one_iff_adj).mpr hδ).le, ?_⟩
      rw [zv_of_not_isMVtx _ hρM]
      exact zh_le_zm _ hδ.symm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨μ, hμ, hdμ, hρμ⟩ := hgen ρ hρ
  refine hρμ.trans ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun ρ' hρ' => ?_
  obtain ⟨μ', hμ', hdμ', hρμ'⟩ := hgen ρ' hρ'
  refine hρμ'.trans (zm_le_centralizer_zm h hμ' hμ ?_)
  have := dist_triangle (puAmalgam h.le) μ' β μ
  rw [tdist_comm _ μ' β] at this
  have hdμ1 : (puAmalgam h.le).treeGraph.dist β μ ≤ 1 := hdμ
  have hdμ'1 : (puAmalgam h.le).treeGraph.dist β μ' ≤ 1 := hdμ'
  omega

end Abelian

section III

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem relIndex_critR0_sup_zm_le (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α') :
    (ZM (puAmalgam h.le) α).relIndex
        (⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ⊔ ZM (puAmalgam h.le) α) ≤
      Fintype.card F := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  obtain ⟨-, hR0, hR⟩ := concl431_i_ii h hC hφ hb hs
  unfold critR0 at hR0
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hR0V : ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans (stab_le_normalizer_vv h α))
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  rw [relIndex_sup_of_le_normalizer ((hR0V.trans hVs).trans (stab_le_normalizer_zm _ α))]
  have hRZ : critR (puAmalgam h.le) α α' ≤ ZM _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans (stab_le_normalizer_zm _ α))
  have hRR0 : critR (puAmalgam h.le) α α' ≤ ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ :=
    Subgroup.commutator_mono (zm_le_vv h hα) le_rfl
  have hβ := adj_geo_one_of_isCritical _ hb0 hs.1
  have hfin : Finite ↥⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ := by
    have := finite_qv _ h20 (by rw [← isMVtx_iff_of_adj _ hβ]; exact hα)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      (hR0V.trans ((vv_le_qv h hb hα).trans (qv_le_qv _ h20 hα hβ))))
  have hne : (critR (puAmalgam h.le) α α').relIndex
      ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  refine (Subgroup.relIndex_le_of_le_left hRZ hne).trans ?_
  have hmul := relIndex_mul_card_inf (critR (puAmalgam h.le) α α')
    ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆
  rw [inf_of_le_left hRR0, hR0, hR, sq] at hmul
  have hq : 0 < Nat.card F := Nat.card_pos
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.eq_of_mul_eq_mul_right hq hmul).le

theorem concl431_iii (hF : S4CFF) (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hH : Hyp40 h φ) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α')
    (hab : ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ ≤ ZM (puAmalgam h.le) α) :
    IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α) :=
  hF G M T L h F inferInstance inferInstance φ hH α' α
    (ms22_iii _ h.hyp20 h.critDist_pos hC hs.1) hab
    (relIndex_critR0_sup_zm_le h hC hH.2.2 hH.2.1 hs)

end III

section V

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem false_of_star_four (hC : CentHyp (puAmalgam h.le)) (hb : 2 < critDist (puAmalgam h.le))
    (hb4 : critDist (puAmalgam h.le) = 4) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α') {q : ℕ}
    (hcγ : IsC1 h.le L q (geo (puAmalgam h.le) α' α 2)
      (Vv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2))
      (ZM (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2))) : False := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = 4 := hs.1.2.1.trans hb4
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = 4 := hc'.2.1.trans hb4
  have hγeq : geo (puAmalgam h.le) α α' 2 = geo (puAmalgam h.le) α' α 2 := by
    rw [← geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist α α' by omega), hd]
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
  have hZγQα : ZM (puAmalgam h.le) γ ≤ Qv _ α := zm_le_qv_of_dist_lt _ hγ (by omega)
  obtain ⟨-, hXα⟩ := vcirc_le_qv_not_le h hfull hC hb hs
  have hαnab : α ∈ nablaSet h.le L γ := by
    refine ⟨hdγα, fun hle => ?_⟩
    rw [zv_of_isMVtx _ hα] at hle
    apply ms22_iv _ h20 hb0 hC hs.1
    rw [hγeq, xm_eq_zm h hfull hγ, stab_eq_ltil_sup_qv_adj h hfull hγ hβγ.symm]
    have hN : stab (puAmalgam h.le) α ⊓ stab _ γ ≤ Subgroup.normalizer
        ((ZM (puAmalgam h.le) α ⊔ ZM (puAmalgam h.le) γ : Subgroup _) : Set _) :=
      (inf_le_inf (stab_le_normalizer_zm _ α) (stab_le_normalizer_zm _ γ)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    refine sup_le ?_ ((le_inf hQβα hQβγ).trans hN)
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    refine S4A.commutator_sup_le_of ((commutator_bloc_le h hb hγ |>.trans' ?_).trans le_sup_right)
      ?_ ?_ ?_
    · exact Subgroup.commutator_mono hle le_rfl
    · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((ltil_le_stab h γ).trans (stab_le_normalizer_zm _ γ))).trans le_sup_right
    · exact (le_inf (hZαQγ.trans (qv_le_stab _ γ) |>.trans' le_rfl |> fun h' =>
        (zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α)) (hZαQγ.trans (qv_le_stab _ γ))).trans hN
    · exact (le_inf (hZγQα.trans (qv_le_stab _ α)) ((zm_le_qv_self _ hγ hb0).trans
        (qv_le_stab _ γ))).trans hN
  obtain ⟨g, hg, hgα⟩ : ∃ g ∈ stab (puAmalgam h.le) γ,
      ¬ (ZM (puAmalgam h.le) α).map (MulAut.conj g).toMonoidHom ≤ Qv _ α := by
    by_contra hcon
    push Not at hcon
    exact hXα ((vcirc_le_conjCl h hfull hb hγ hcγ hαnab).trans
      (iSup₂_le fun g hg => hcon g hg))
  have hg' : g ∈ ((Ltil h.le L γ ⊔ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) :
      Subgroup _) : Set _) := stab_eq_ltil_sup_qv_adj h hfull hγ hβγ.symm ▸ hg
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
  have hBγ := (isC1_bloc h hfull hb hγ hcγ).1
  have hQZB : ⁅Qv (puAmalgam h.le) γ, ZM (puAmalgam h.le) α⁆ ≤ Bloc h.le L γ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hZαVγ le_rfl).trans hBγ
  have hQZα : ⁅Qv (puAmalgam h.le) γ, ZM (puAmalgam h.le) α⁆ ≤ ZM _ α :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (((qv_le_qv _ h20 hγ hβγ.symm).trans hQβα).trans (stab_le_normalizer_zm _ α))
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
  have hcen : ZM (puAmalgam h.le) α ⊔ ZM (puAmalgam h.le) γ ≤ centerOf (Vv (puAmalgam h.le) α) := by
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
  have hVL := commutator_vv_ltil_le_of h hfull hα hαβ hZβ hZα'' hcn (hcomm.trans hcen)
  have hβH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  have hVi := vi_one_comm_eq_bot h hb hβH
  have hVle := (vv_le_vi_sup_commutator h hfull hα hαβ).trans (sup_le_sup_left hVL _)
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

end V

section Props

theorem s43b4_of (hF : S4CFF) (h32 : S32) (hAb : S43b4Ab) : S43b4 := by
  intro G _ _ M T L h F _ _ φ hH hb4 α α' hs
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hH.2.2⟩
  have hC := centHyp_of_S32 h32 h
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hs.1
  have hγ := isMVtx_geo_two _ h.hyp20 h.critDist_pos hc'
  obtain ⟨γ', hsγ⟩ := exists_star_at _ hs hγ
  have hcγ := concl431_iii h hF hC hH hsγ (hAb G M T L h F inferInstance inferInstance φ hH hb4 _ _
    hsγ)
  exact false_of_star_four h hfull hC hH.2.1 hb4 hs hcγ

theorem s431A_of (hF : S4CFF) (h32 : S32) (h4 : S43b4) : S431A := by
  intro G _ _ M T L h F _ _ φ hH α α' hs
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hH.2.2⟩
  have hC := centHyp_of_S32 h32 h
  have hb := hH.2.1
  have hb6 : 6 ≤ critDist (puAmalgam h.le) := by
    have hne : critDist (puAmalgam h.le) ≠ 4 := fun h4' =>
      h4 G M T L h F inferInstance inferInstance φ hH h4' α α' hs
    obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
    omega
  have hab := vv_comm_eq_bot h (by omega) hs.1.1
  have hc1 := concl431_iii h hF hC hH hs (by rw [hab]; exact bot_le)
  obtain ⟨hR0U, hR0, hR⟩ := concl431_i_ii h hC hH.2.2 hb hs
  rw [Nat.card_eq_fintype_card (α := F)] at hR0 hR
  exact ⟨hR0U, hR0, hR, hc1, fun δ hδ => vcirc_le_conjCl h hfull hb hs.1.1 hc1 hδ, hb6⟩

theorem s431B_of (h32 : S32) (h431A : S431A) : S431B := by
  intro G _ _ M T L h F _ _ φ hH α α' hs
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hH.2.2⟩
  have hC := centHyp_of_S32 h32 h
  have hb := hH.2.1
  have hcα := (h431A G M T L h F inferInstance inferInstance φ hH α α' hs).2.2.2.1
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hs.1
  have hγ := isMVtx_geo_two _ h.hyp20 h.critDist_pos hc'
  obtain ⟨γ', hsγ⟩ := exists_star_at _ hs hγ
  have hcγ := (h431A G M T L h F inferInstance inferInstance φ hH _ γ' hsγ).2.2.2.1
  obtain ⟨h6a, h6b⟩ := concl431_vi h hfull hC hb hH.2.2 hs hcα
  exact ⟨h6a, h6b, fun δ hδ => concl431_vii h hfull hC hb hH.2.2 hs hcα hcγ hδ⟩

end Props

end CFSG.Quasithin.MS93.S4A
