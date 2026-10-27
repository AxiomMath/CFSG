module

public import CFSG.Quasithin.MS93.S4A44E1
public import CFSG.Quasithin.MS93.S4A433
public import CFSG.Quasithin.MS93.S4A44Inputs

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Transport

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem usup_le_dloc_transport_inv (hfull : IsSL3Full M T L) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') (hs : IsStraight (puAmalgam h.le) α α') {j : ℕ}
    (hj : 2 ≤ j) (hjb : 2 * j < critDist (puAmalgam h.le))
    (hle : Usup (puAmalgam h.le) (geo (puAmalgam h.le) α α' (2 * j - 2))
        (geo (puAmalgam h.le) α α' (2 * j - 3)) ≤
      Dloc h.le L (geo (puAmalgam h.le) α α' (2 * j - 4))) :
    Usup (puAmalgam h.le) (geo (puAmalgam h.le) α α' (2 * j + 2))
        (geo (puAmalgam h.le) α α' (2 * j + 1)) ≤
      Dloc h.le L (geo (puAmalgam h.le) α α' (2 * j)) := by
  obtain ⟨s₁, hs₁, hs₁a, hs₁b⟩ := exists_ltil_mirror h hfull hc hs (j := j) (by omega) hjb
  obtain ⟨s₀, hs₀, hs₀a, hs₀b⟩ := exists_ltil_mirror h hfull hc hs (j := j - 1) (by omega)
    (by omega)
  have e₀ : 2 * (j - 1) = 2 * j - 2 := by omega
  have e₂ : 2 * (j - 1) + 2 = 2 * j := by omega
  have e₂' : 2 * (j - 1) - 2 = 2 * j - 4 := by omega
  have e₁ : 2 * (j - 1) + 1 = 2 * j - 1 := by omega
  have e₁' : 2 * (j - 1) - 1 = 2 * j - 3 := by omega
  rw [e₂, e₂'] at hs₀a
  rw [e₁, e₁'] at hs₀b
  rw [e₀] at hs₀
  have hs₀s : s₀ • geo (puAmalgam h.le) α α' (2 * j - 2) = geo (puAmalgam h.le) α α' (2 * j - 2) :=
    (mem_stab _).mp (ltil_le_stab h _ hs₀)
  have e1 : geo (puAmalgam h.le) α α' (2 * j + 2) =
      (s₀ * s₁)⁻¹ • geo (puAmalgam h.le) α α' (2 * j - 2) := by
    rw [eq_inv_smul_iff, mul_smul, hs₁a, hs₀s]
  have e2 : geo (puAmalgam h.le) α α' (2 * j + 1) =
      (s₀ * s₁)⁻¹ • geo (puAmalgam h.le) α α' (2 * j - 3) := by
    rw [eq_inv_smul_iff, mul_smul, hs₁b, hs₀b]
  have e3 : geo (puAmalgam h.le) α α' (2 * j) =
      (s₀ * s₁)⁻¹ • geo (puAmalgam h.le) α α' (2 * j - 4) := by
    rw [eq_inv_smul_iff, mul_smul, (mem_stab _).mp (ltil_le_stab h _ hs₁), hs₀a]
  rw [e1, e2, e3, usup_smul, dloc_smul h]
  exact Subgroup.map_mono hle

end Transport

section Straight

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem usup_le_dloc_of_straight (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    (h444 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      IsStraight (puAmalgam h.le) δ δ' → Concl444 h.le δ δ')
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hs : IsStraight (puAmalgam h.le) α α') :
    Usup (puAmalgam h.le) α' (geo _ α' α 1) ≤ Dloc h.le L (geo _ α' α 2) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hsym : ∀ m, m ≤ critDist (puAmalgam h.le) →
      geo (puAmalgam h.le) α' α m = geo _ α α' (critDist (puAmalgam h.le) - m) := fun m hm => by
    have := geo_symm (puAmalgam h.le) (u := α) (w := α') (i := critDist (puAmalgam h.le) - m)
      (by omega)
    rwa [hd, show critDist (puAmalgam h.le) - (critDist (puAmalgam h.le) - m) = m by omega]
      at this
  obtain ⟨-, hD, -⟩ := inf_centralizer_eq_usup h hφ hC hb6 hV h441 h444 hc hs
  rw [hsym 4 (by omega), hsym 5 (by omega), hsym 6 (by omega)] at hD
  have := usup_le_dloc_transport_inv h hfull hc hs (j := k - 1) (by omega) (by omega) (by
    rw [show 2 * (k - 1) - 2 = critDist (puAmalgam h.le) - 4 by omega,
      show 2 * (k - 1) - 3 = critDist (puAmalgam h.le) - 5 by omega,
      show 2 * (k - 1) - 4 = critDist (puAmalgam h.le) - 6 by omega]
    exact hD)
  rw [show 2 * (k - 1) + 2 = critDist (puAmalgam h.le) by omega,
    show 2 * (k - 1) + 1 = critDist (puAmalgam h.le) - 1 by omega,
    show 2 * (k - 1) = critDist (puAmalgam h.le) - 2 by omega] at this
  rw [hsym 1 (by omega), hsym 2 (by omega)]
  have e : geo (puAmalgam h.le) α α' (critDist (puAmalgam h.le)) = α' := by rw [← hd, geo_dist]
  rwa [e] at this

end Straight

section Nabla

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem mem_nablaSet_of_isCritical (hC : CentHyp (puAmalgam h.le))
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') :
    α ∈ nablaSet h.le L (geo (puAmalgam h.le) α α' 2) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2) := isMVtx_geo_two _ h20 hb0 hc
  have hαβ : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α α' 1) :=
    adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α α' 1)
      (geo (puAmalgam h.le) α α' 2) := adj_geo _ (i := 1) (by omega)
  have hdαγ : (puAmalgam h.le).treeGraph.dist α (geo (puAmalgam h.le) α α' 2) = 2 :=
    dist_geo _ (by omega)
  have hdγα : (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) α α' 2) α = 2 := by
    rw [tdist_comm]; exact hdαγ
  have hQβα : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) ≤ stab _ α :=
    qv_le_stab_of_adj _ hαβ.symm
  have hQβγ : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) ≤
      stab _ (geo (puAmalgam h.le) α α' 2) := qv_le_stab_of_adj _ hβγ
  have hZαQγ : ZM (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α α' 2) :=
    zm_le_qv_of_dist_lt _ hα (by omega)
  have hZγQα : ZM (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2) ≤ Qv _ α :=
    zm_le_qv_of_dist_lt _ hγ (by rw [hdγα]; omega)
  refine ⟨hdγα, fun hle => ?_⟩
  rw [zv_of_isMVtx _ hα] at hle
  apply ms22_iv _ h20 hb0 hC hc
  rw [xm_eq_zm h hfull hγ, stab_eq_ltil_sup_qv_adj h hfull hγ hβγ.symm]
  have hN : stab (puAmalgam h.le) α ⊓ stab _ (geo (puAmalgam h.le) α α' 2) ≤
      Subgroup.normalizer ((ZM (puAmalgam h.le) α ⊔
        ZM (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2) : Subgroup _) : Set _) :=
    (inf_le_inf (stab_le_normalizer_zm _ α) (stab_le_normalizer_zm _ _)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  refine sup_le ?_ ((le_inf hQβα hQβγ).trans hN)
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  refine S4A.commutator_sup_le_of
    (((Subgroup.commutator_mono hle le_rfl).trans (commutator_bloc_le h hb hγ)).trans
      le_sup_right) ?_ ?_ ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h _).trans (stab_le_normalizer_zm _ _))).trans le_sup_right
  · exact (le_inf ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α))
      (hZαQγ.trans (qv_le_stab _ _))).trans hN
  · exact (le_inf (hZγQα.trans (qv_le_stab _ α)) ((zm_le_qv_self _ hγ hb0).trans
      (qv_le_stab _ _))).trans hN

end Nabla

section EndVQ

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem commutator_vv_qv_le_dloc_of (h42 : S42) (hmin : PUMin M T L)
    (hC : CentHyp (puAmalgam h.le)) (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    (h444 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      IsStraight (puAmalgam h.le) δ δ' → Concl444 h.le δ δ')
    (hc1 : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
      IsC1 h.le L (Fintype.card F) μ (Vv (puAmalgam h.le) μ) (ZM (puAmalgam h.le) μ))
    (hex : ∃ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' ∧
      IsStraight (puAmalgam h.le) α α')
    {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) :
    ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨α₀, α₀', hc₀, hs₀⟩ := hex
  have hd₀ : (puAmalgam h.le).treeGraph.dist α₀' α₀ = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hc₀.2.1
  have hν₀ : IsMVtx (puAmalgam h.le) (geo _ α₀' α₀ 2) := isMVtx_geo_two _ h.hyp20 hb0
    (ms22_iii _ h.hyp20 hb0 hC hc₀)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hν₀ hμ
  have hc : IsCritical (puAmalgam h.le) (g • α₀) (g • α₀') := (isCritical_smul _ g _ _).mpr hc₀
  have hs : IsStraight (puAmalgam h.le) (g • α₀) (g • α₀') := (isStraight_smul _ g _ _).mpr hs₀
  have hgeo : geo (puAmalgam h.le) (g • α₀') (g • α₀) 2 = μ := by rw [geo_smul, hg]
  have hU := usup_le_dloc_of_straight h hφ hC hb6 hV h441 h444 hc hs
  rw [hgeo] at hU
  have hc' := ms22_iii _ h.hyp20 hb0 hC hc
  have hnab := mem_nablaSet_of_isCritical h hfull hC hb2 hc'
  rw [hgeo] at hnab
  have hVc := vcirc_le_conjCl h hfull hb2 hμ (hc1 μ hμ) hnab
  have hd' : (puAmalgam h.le).treeGraph.dist (g • α₀') (g • α₀) = critDist (puAmalgam h.le) :=
    hc'.2.1
  have hμρ : (puAmalgam h.le).treeGraph.Adj μ (geo _ (g • α₀') (g • α₀) 1) := by
    rw [← hgeo]
    exact (adj_geo _ (i := 1) (by omega)).symm
  have hZμ : ZM (puAmalgam h.le) (g • α₀') ≤ stab _ μ :=
    (zm_le_qv_of_dist_lt _ hc'.1 (by rw [← hgeo, dist_geo _ (by omega)]; omega)).trans
      (qv_le_stab _ μ)
  have hKL : ⁅ZM (puAmalgam h.le) (g • α₀'), Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ := by
    refine le_trans ?_ hU
    rw [Usup, zv_of_isMVtx _ hc'.1]
    exact Subgroup.commutator_mono le_rfl (qv_le_qv _ h.hyp20 hμ hμρ)
  have hVQ : ⁅Vcirc h.le L μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ :=
    (Subgroup.commutator_mono hVc le_rfl).trans (commutator_conjCl_le
      (stab_le_normalizer_dloc h μ) (stab_le_normalizer_qv _ μ)
      (hZμ.trans (stab_le_normalizer_dloc h μ)) hKL)
  exact (h42 G M T L h hmin hb2 F inferInstance inferInstance φ hφ μ _ hμ hμρ).2 _
    (stab_le_normalizer_qv _ μ) le_rfl hVQ

theorem usup_le_zh_of_nabla (h42 : S42) (hmin : PUMin M T L) (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le)) {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hnab : ∀ δ, (puAmalgam h.le).treeGraph.Adj β δ → δ ∈ nablaSet h.le L α →
      Usup (puAmalgam h.le) δ β ≤ Dloc h.le L α) :
    Usup (puAmalgam h.le) α β ≤ ZH (puAmalgam h.le) β := by
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  refine (h42 G M T L h hmin hb2 F inferInstance inferInstance φ hφ α β hα hαβ).1
    (fun δ hβδ => ?_) (card_usup_eq_sq h hφ hC hb hα hαβ)
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have h1 := isMVtx_iff_of_adj _ hαβ
    have h2 := isMVtx_iff_of_adj _ hβδ
    tauto
  have hUZ : Usup (puAmalgam h.le) δ β ≤ Zv _ δ := by
    rw [Usup, zv_of_isMVtx _ hδM]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hβδ).trans (stab_le_normalizer_zm _ δ))
  by_cases hδα : δ = α
  · subst hδα
    exact hUZ.trans (by rw [zv_of_isMVtx _ hα]; exact zm_le_bloc h hb2 hα)
  have hd : (puAmalgam h.le).treeGraph.dist α δ = 2 :=
    dist_eq_two_of_adj_adj _ hαβ hβδ (Ne.symm hδα)
  by_cases hn : δ ∈ nablaSet h.le L α
  · intro x hx
    rw [mem_bloc_iff h hb2 hα]
    refine ⟨zv_le_vv h hd.le (hUZ hx), fun l hl => ?_⟩
    have hxl : x * l = l * x :=
      (Subgroup.mem_centralizer_iff.mp (dloc_le_centralizer_ltil h hα (hnab δ hβδ hn hx)) l hl).symm
    rw [commutatorElement_def, hxl, mul_inv_cancel_right, mul_inv_cancel]
    exact (ZM (puAmalgam h.le) α).one_mem
  · have hZB : Zv (puAmalgam h.le) δ ≤ Bloc h.le L α := by
      by_contra hcon
      exact hn ⟨hd, hcon⟩
    exact hUZ.trans hZB

omit hφ in
theorem commutator_vv_qv_le_stabCenter_of (hfull : IsSL3Full M T L)
    (hb : 2 < critDist (puAmalgam h.le))
    (hU : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH (puAmalgam h.le) ρ)
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hD : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Dloc h.le L α)
    (hUD : Uloc h.le L α ⊓ Dloc h.le L α = ⊥) :
    ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ stabCenter (puAmalgam h.le) α := by
  have hZ := commutator_vv_qv_le_zm h hb hU hα
  have hzc := zloc_le_centralizer_stab h hfull hα
  have hzs : Zloc h.le L α ≤ stab (puAmalgam h.le) α :=
    (zloc_le_zm h hfull hα).trans ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ α))
  intro x hx
  have hxZ := hZ hx
  rw [zm_eq_uloc_sup_zloc h hfull hα] at hxZ
  have hn : Uloc h.le L α ≤
      Subgroup.normalizer (Zloc h.le L α : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_le_centralizer ?_
    refine (uloc_le_zm h hfull hα).trans ((zm_le_qv_self _ hα h.critDist_pos).trans
      ((qv_le_stab _ α).trans ?_))
    exact Subgroup.le_centralizer_iff.mp hzc
  have hxZ' : x ∈ ((Uloc h.le L α ⊔ Zloc h.le L α : Subgroup _) :
      Set (puAmalgam h.le).Universal) := hxZ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hxZ'
  obtain ⟨u, hu, z, hz, rfl⟩ := hxZ'
  have huD : u ∈ Dloc h.le L α := by
    have : u = u * z * z⁻¹ := by group
    rw [this]
    exact (Dloc h.le L α).mul_mem (hD hx) ((Dloc h.le L α).inv_mem (zloc_le_dloc h α hz))
  have hu1 : u = 1 := by
    have : u ∈ Uloc h.le L α ⊓ Dloc h.le L α := ⟨hu, huD⟩
    rw [hUD, Subgroup.mem_bot] at this
    exact this
  change u * z ∈ _
  rw [hu1, one_mul]
  refine ⟨⟨z, hzs hz⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  simpa using Subgroup.mem_centralizer_iff.mp (hzc hz) g g.2

end EndVQ

section Straight2

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem isStraight_symm (h : Hyp20 X) {α α' : Vtx X} (hc : IsCritical X α α')
    (hs : IsStraight X α α') : IsStraight X α' α := by
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  obtain ⟨k, hk⟩ := ms21_v X h
  have hsym : ∀ m, m ≤ critDist X → geo X α' α m = geo X α α' (critDist X - m) := fun m hm => by
    have := geo_symm X (u := α) (w := α') (i := critDist X - m) (by omega)
    rwa [hd, show critDist X - (critDist X - m) = m by omega] at this
  intro i hi0 hib
  rw [tdist_comm, hd] at hib
  obtain ⟨g, hg, hge⟩ := hs (k - i) (by omega) (by rw [hd]; omega)
  refine ⟨g⁻¹, ?_, ?_⟩
  · rw [hsym _ (by omega), show critDist X - 2 * i = 2 * (k - i) by omega]
    exact inv_mem hg
  · rw [hsym _ (by omega), hsym _ (by omega), inv_smul_eq_iff,
      show critDist X - (2 * i + 2) = 2 * (k - i) - 2 by omega,
      show critDist X - (2 * i - 2) = 2 * (k - i) + 2 by omega, hge]

theorem IsGoodPathB.isStraight {p : ℕ → Vtx X} {N : ℕ} (hp : IsGoodPathB X p N) {i : ℕ}
    (hie : Even i) (hiN : i + critDist X ≤ N) (hb : 0 < critDist X) (h : Hyp20 X) :
    IsStraight X (p (i + critDist X)) (p i) := by
  have hnb := hp.toIsNBPath
  obtain ⟨k, hk⟩ := ms21_v X h
  obtain ⟨l, hl⟩ := hie
  have hd : X.treeGraph.dist (p (i + critDist X)) (p i) = critDist X := by
    rw [tdist_comm, hnb.dist_eq' (by omega) hiN]; omega
  intro m hm0 hmb
  rw [hd] at hmb
  have hgeo : ∀ j, j ≤ critDist X → geo X (p (i + critDist X)) (p i) j = p (i + critDist X - j) :=
    fun j hj => by
      rw [hnb.eq_geo_rev (i := i) (j := i + critDist X) (k := i + critDist X - j) (by omega)
        (by omega) hiN]
      congr 1
      omega
  obtain ⟨g, hg, hge⟩ := hp.straight (i + critDist X - 2 * m) ⟨l + k - m, by omega⟩ (by omega)
    (by omega)
  refine ⟨g⁻¹, ?_, ?_⟩
  · rw [hgeo _ (by omega)]
    exact inv_mem hg
  · rw [hgeo _ (by omega), hgeo _ (by omega), inv_smul_eq_iff,
      show i + critDist X - (2 * m - 2) = i + critDist X - 2 * m + 2 by omega, hge,
      show i + critDist X - (2 * m + 2) = i + critDist X - 2 * m - 2 by omega]

end Straight2

section EndOrders

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem sq_le_relIndex_qv_of_straight (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    (h444 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      IsStraight (puAmalgam h.le) δ δ' → Concl444 h.le δ δ')
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hs : IsStraight (puAmalgam h.le) α α') :
    Fintype.card F ^ 2 ≤
      (Qv (puAmalgam h.le) (geo _ α' α 4)).relIndex (Qv (puAmalgam h.le) (geo _ α' α 5)) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hα' := hc.isMVtx_right _ h.hyp20
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hc.2.1
  obtain ⟨-, -, x₁, x₂, hc₁, hc₂, hQ₁, hQ₂, hdisj⟩ :=
    inf_centralizer_eq_usup h hφ hC hb6 hV h441 h444 hc hs
  have hz : IsMVtx (puAmalgam h.le) (geo _ α' α 4) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => ⟨2, rfl⟩, fun _ => hα'⟩
  have hzε : (puAmalgam h.le).treeGraph.Adj (geo _ α' α 4) (geo _ α' α 5) := adj_geo _ (by omega)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hz
  have hs₁ : ZM (puAmalgam h.le) x₁ ≤ stab _ (geo _ α' α 4) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 (ms22_iii _ h.hyp20 hb0 hC hc₁)
  have hs₂ : ZM (puAmalgam h.le) x₂ ≤ stab _ (geo _ α' α 4) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 (ms22_iii _ h.hyp20 hb0 hC hc₂)
  have hεs : Qv (puAmalgam h.le) (geo _ α' α 5) ≤ stab _ (geo _ α' α 4) :=
    qv_le_stab_of_adj _ hzε.symm
  have hE : natImage ψ (ZM (puAmalgam h.le) x₁) ⊓ natImage ψ (ZM (puAmalgam h.le) x₂) = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hg₁, hg₂⟩
    rw [Subgroup.mem_bot]
    refine eq_one_of_mulVec_eq_self fun v => ?_
    have hw₁ := sub_mem_commN hg₁ v
    have hw₂ := sub_mem_commN hg₂ v
    obtain ⟨u, hu⟩ := natVec_surjective hψ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v)
    rw [← hu, ← mem_commutator_iff_natVec hψ hs₁ u,
      ← commutator_zm_eq_uloc h hfull hz hs₁, Subgroup.commutator_comm] at hw₁
    rw [← hu, ← mem_commutator_iff_natVec hψ hs₂ u,
      ← commutator_zm_eq_uloc h hfull hz hs₂, Subgroup.commutator_comm] at hw₂
    have hu1 : u = 1 := by
      apply Subtype.ext
      have : (u : (puAmalgam h.le).Universal) ∈ (⊥ : Subgroup _) := hdisj ▸ ⟨hw₁, hw₂⟩
      exact (Subgroup.mem_bot).mp this
    have : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v = 0 := by rw [← hu, hu1, natVec_one]
    exact sub_eq_zero.mp this
  have hq₁ : Fintype.card F ≤ Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) x₁)) := by
    rw [S46.card_natImage_eq_relIndex h hφ hz hψ hs₁, ← Nat.card_eq_fintype_card]
    exact le_relIndex_zm_of_isCritical h hC hφ hc₁
  have hq₂ : Fintype.card F ≤ Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) x₂)) := by
    rw [S46.card_natImage_eq_relIndex h hφ hz hψ hs₂, ← Nat.card_eq_fintype_card]
    exact le_relIndex_zm_of_isCritical h hC hφ hc₂
  have hsup := card_mul_card_le_card_sup hE
  have hle : natImage ψ (ZM (puAmalgam h.le) x₁) ⊔ natImage ψ (ZM (puAmalgam h.le) x₂) ≤
      natImage ψ (Qv (puAmalgam h.le) (geo _ α' α 5)) :=
    sup_le (natImage_mono hQ₁) (natImage_mono hQ₂)
  rw [← S46.card_natImage_eq_relIndex h hφ hz hψ hεs, sq]
  exact (Nat.mul_le_mul hq₁ hq₂).trans (hsup.trans (Subgroup.card_le_of_le hle))

end EndOrders

section EndB

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem critDist_eq_eight_of (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    (h444 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      IsStraight (puAmalgam h.le) δ δ' → Concl444 h.le δ δ')
    (hU : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH (puAmalgam h.le) ρ)
    (hex : ∃ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' ∧
      IsStraight (puAmalgam h.le) α α') :
    critDist (puAmalgam h.le) = 8 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  by_contra hne
  obtain ⟨α₀, α₀', hc₀, hs₀⟩ := hex
  obtain ⟨p, hp, -⟩ := exists_isGoodPathB h hb h444
    (fun δ δ' hc => exists_adj_not_le_normalizer_usup h hφ hC hb hc) hc₀ hs₀ 4
  rw [show critDist (puAmalgam h.le) + 2 * 4 = critDist (puAmalgam h.le) + 8 by omega] at hp
  have hnb := hp.toIsNBPath
  have hM : ∀ i, Even i → i ≤ critDist (puAmalgam h.le) + 8 → IsMVtx (puAmalgam h.le) (p i) :=
    fun i hi hiN => (hnb.isMVtx_iff hiN).mpr ⟨fun _ => hi, fun _ => hp.mvtx⟩
  have hd : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i := fun i j hij hj => hnb.dist_eq' hij hj
  have hc4 : IsCritical (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) (p 4) := by
    have := hp.crit 4 ⟨2, rfl⟩ (by omega)
    rwa [show 4 + critDist (puAmalgam h.le) = critDist (puAmalgam h.le) + 4 by omega] at this
  have hs4 : IsStraight (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) (p 4) := by
    have := hp.isStraight _ (i := 4) ⟨2, rfl⟩ (by omega) hb0 h.hyp20
    rwa [show 4 + critDist (puAmalgam h.le) = critDist (puAmalgam h.le) + 4 by omega] at this
  have hα := hM (critDist (puAmalgam h.le) + 4) ⟨k + 2, by omega⟩ (by omega)
  have hp8 := hM 8 ⟨4, rfl⟩ (by omega)
  have hβα : (puAmalgam h.le).treeGraph.Adj (p (critDist (puAmalgam h.le) + 3))
      (p (critDist (puAmalgam h.le) + 4)) := hp.adj _ (by omega)
  have hgeo : ∀ j, j ≤ critDist (puAmalgam h.le) →
      geo (puAmalgam h.le) (p 4) (p (critDist (puAmalgam h.le) + 4)) j = p (4 + j) := fun j hj => by
    rw [hnb.eq_geo (i := 4) (j := critDist (puAmalgam h.le) + 4) (k := 4 + j) (by omega)
      (by omega) (by omega)]
    congr 1
    omega
  have hgeo' : ∀ j, j ≤ critDist (puAmalgam h.le) →
      geo (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) (p 4) j =
        p (critDist (puAmalgam h.le) + 4 - j) := fun j hj => by
    rw [hnb.eq_geo_rev (i := 4) (j := critDist (puAmalgam h.le) + 4)
      (k := critDist (puAmalgam h.le) + 4 - j) (by omega) (by omega) (by omega)]
    congr 1
    omega
  obtain ⟨hCeq, -, -⟩ := inf_centralizer_eq_usup h hφ hC hb6 hV h441 h444 hc4 hs4
  rw [hgeo 4 (by omega), hgeo 5 (by omega)] at hCeq
  have hUZ := hU _ _ hα hβα.symm
  have hZ4β : ZM (puAmalgam h.le) (p 4) ≤ Qv _ (p (critDist (puAmalgam h.le) + 3)) :=
    zm_le_qv_of_dist_lt _ (hM 4 ⟨2, rfl⟩ (by omega)) (by rw [hd 4 _ (by omega) (by omega)]; omega)
  have hUC : Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
      (p (critDist (puAmalgam h.le) + 3)) ≤ Uloc h.le L (p (critDist (puAmalgam h.le) + 4)) ⊓
        Subgroup.centralizer (ZM (puAmalgam h.le) (p 4) : Set (puAmalgam h.le).Universal) :=
    le_inf (usup_le_uloc h hφ hα hβα.symm)
      (hUZ.trans ((zh_le_centralizer _ _).trans (Subgroup.centralizer_le hZ4β)))
  rw [hCeq] at hUC
  have hp89 : (puAmalgam h.le).treeGraph.Adj (p 8) (p (4 + 5)) := hp.adj 8 (by omega)
  have hfin : Finite ↥(Usup (puAmalgam h.le) (p (4 + 4)) (p (4 + 5))) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_usup_eq_sq h hφ hC hb hp8 hp89]
      exact pow_ne_zero _ Fintype.card_ne_zero)
  have hUeq := Subgroup.eq_of_le_of_card_ge hUC (by
    rw [card_usup_eq_sq h hφ hC hb hp8 hp89, card_usup_eq_sq h hφ hC hb hα hβα.symm])
  have hcr := ms22_iii _ h.hyp20 hb0 hC hc4
  have hD := usup_le_dloc_of_straight h hφ hC hb6 hV h441 h444 hcr
    (isStraight_symm _ h.hyp20 hc4 hs4)
  rw [hgeo' 1 (by omega), hgeo' 2 (by omega),
    show critDist (puAmalgam h.le) + 4 - 1 = critDist (puAmalgam h.le) + 3 by omega,
    show critDist (puAmalgam h.le) + 4 - 2 = critDist (puAmalgam h.le) + 2 by omega] at hD
  have hmir := hp.usup_eq_of_le_dloc h hfull (i := critDist (puAmalgam h.le) + 2)
    ⟨k + 1, by omega⟩ (by omega) (by omega) hD (Or.inl (by
      rw [show critDist (puAmalgam h.le) + 2 + 2 = critDist (puAmalgam h.le) + 4 by omega,
        show critDist (puAmalgam h.le) + 2 + 1 = critDist (puAmalgam h.le) + 3 by omega]))
  rw [show critDist (puAmalgam h.le) + 2 + 2 = critDist (puAmalgam h.le) + 4 by omega,
    show critDist (puAmalgam h.le) + 2 + 1 = critDist (puAmalgam h.le) + 3 by omega,
    show critDist (puAmalgam h.le) + 2 - 2 = critDist (puAmalgam h.le) by omega,
    show critDist (puAmalgam h.le) + 2 - 1 = critDist (puAmalgam h.le) + 1 by omega] at hmir
  have hpe := hp.pe (critDist (puAmalgam h.le)) ⟨k, hk⟩ le_rfl (by omega)
  rw [Nat.sub_self] at hpe
  apply hpe
  rw [← hmir, hUeq]
  refine le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp ?_)
  have hUZ8 : Usup (puAmalgam h.le) (p (4 + 4)) (p (4 + 5)) ≤ ZM (puAmalgam h.le) (p 8) := by
    rw [Usup, zv_of_isMVtx _ hp8]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hp89.symm).trans (stab_le_normalizer_zm _ _))
  exact hUZ8.trans ((zm_le_centralizer_qv _ h.hyp20 hp8).trans (Subgroup.centralizer_le
    (zm_le_qv_of_dist_lt _ (hM 0 ⟨0, rfl⟩ (by omega)) (by
      rw [hd 0 8 (by omega) (by omega)]; omega))))

end EndB

theorem s44End_of (h32 : S32) (h43 : S43) (h441 : S441) (h442 : S442) (hFFc : S4CFFc)
    (hNab : EndNabla) : S44End := by
  intro G _ _ M T L h F _ _ φ hH hb
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hH.2.2⟩
  have hC := centHyp_of_S32 h32 h
  have hb6 := s443_of h32 h441 h442 G M T L h F inferInstance inferInstance φ hH hb
  have hV := h43 G M T L h hH.1 hH.2.1 hfull
  have h441' := h441 G M T L h F inferInstance inferInstance φ hH hb
  have h444 := s444_of h32 h43 h441 G M T L h F inferInstance inferInstance φ hH hb
  have hc1 := s445_of h32 h43 h441 h442 hFFc G M T L h F inferInstance inferInstance φ hH hb
  have hex := h442 G M T L h F inferInstance inferInstance φ hH hb
  have h42 := s42_of h32
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hU : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH (puAmalgam h.le) ρ := fun δ ρ hδ hδρ =>
    usup_le_zh_of_nabla h hH.2.2 h42 hH.1 hC hb hδ hδρ fun ε hρε hε =>
      hNab G M T L h F inferInstance inferInstance φ hH hb δ ρ ε hδ hδρ hρε hε
  refine ⟨critDist_eq_eight_of h hH.2.2 hC hb6 hV h441' h444 hU hex, fun α β hα hαβ => ?_⟩
  have hsq : Nat.card ↥(Usup (puAmalgam h.le) α β) = Nat.card F ^ 2 := by
    rw [card_usup_eq_sq h hH.2.2 hC hb hα hαβ, Nat.card_eq_fintype_card]
  refine ⟨commutator_vv_qv_le_stabCenter_of h hfull hb2 hU hα
      (commutator_vv_qv_le_dloc_of h hH.2.2 h42 hH.1 hC hb6 hV h441' h444 hc1 hex hα)
      (uloc_inf_dloc h hH.2.2 α), ?_, ?_⟩
  · rw [relIndex_zh_zm h hfull hH.2.2 hα hαβ (hU α β hα hαβ) hsq, Nat.card_eq_fintype_card]
  · refine le_antisymm ?_ ?_
    · have := relIndex_qv_qv_le h hfull hH.2.2 hα hαβ (hU α β hα hαβ) hsq
      rwa [Nat.card_eq_fintype_card] at this
    · obtain ⟨α₀, α₀', hc₀, hs₀⟩ := hex
      have hlow := sq_le_relIndex_qv_of_straight h hH.2.2 hC hb6 hV h441' h444 hc₀ hs₀
      have hd₀ : (puAmalgam h.le).treeGraph.dist α₀' α₀ = critDist (puAmalgam h.le) := by
        rw [tdist_comm]; exact hc₀.2.1
      have hz : IsMVtx (puAmalgam h.le) (geo _ α₀' α₀ 4) :=
        (isMVtx_geo _ (by omega)).mpr ⟨fun _ => ⟨2, rfl⟩, fun _ => hc₀.isMVtx_right _ h.hyp20⟩
      exact hlow.trans (relIndex_qv_qv_eq h hz (adj_geo _ (by omega)) hα hαβ).ge

end CFSG.Quasithin.MS93.S4A
