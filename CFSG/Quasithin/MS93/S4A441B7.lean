module

public import CFSG.Quasithin.MS93.S4A44Nabla

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Nabla

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem mem_nablaSet_of_conj (hC : CentHyp (puAmalgam h.le))
    (hb : 2 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' μ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hconj : ∃ g : (puAmalgam h.le).Universal,
      g • μ = α ∧ g • α = geo (puAmalgam h.le) α α' 2) :
    μ ∈ nablaSet h.le L α := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨k, hk⟩ := ms21_v _ h20
  obtain ⟨ρ, hρc, hρα⟩ := exists_isCritical_back _ h20 hb0 hV hc (k - 1) (by omega)
  rw [show critDist (puAmalgam h.le) - 2 * (k - 1) = 2 by omega] at hρc
  have hγc := ms22_iii _ h20 hb0 hC hρc
  have hγα : (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) α α' 2) α = 2 := by
    rw [tdist_comm]
    exact dist_geo _ (by omega)
  have hρα' : (puAmalgam h.le).treeGraph.dist ρ α = critDist (puAmalgam h.le) - 2 := by
    rw [hρα]
    omega
  have hgeo : α = geo (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2) ρ 2 := by
    apply eq_geo_of_dist _ hγα
    rw [hγα, tdist_comm _ α ρ, hρα', tdist_comm _ _ ρ, hρc.2.1]
    omega
  have hα := geo_two_mem_nablaSet h hfull hC hb hV hγc
  rw [← hgeo] at hα
  obtain ⟨g, hgμ, hgα⟩ := hconj
  have e := (mem_nablaSet_smul h g α μ).mp
  rw [hgμ, hgα] at e
  exact e hα

end Nabla

section UD

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem commutator_zm_qv_le_of_le_bloc (hb : 2 < critDist (puAmalgam h.le))
    {α μ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hdμ : (puAmalgam h.le).treeGraph.dist α μ = 2)
    (hB : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α)
    (hH : ¬ ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Dloc h.le L α) :
    ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Uloc h.le L α ⊔ Dloc h.le L α := by
  have h20 := h.hyp20
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hμM : IsMVtx _ μ := by
    rcases isMVtx_of_dist_le_two h hα hdμ.le with hM | hadj
    · exact hM
    · rw [dist_eq_one_of_adj _ hadj] at hdμ
      omega
  have hαβ : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α μ 1) :=
    adj_geo_one _ (by omega)
  have hβμ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α μ 1) μ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := μ) (i := 1) (by omega)
    rwa [show geo (puAmalgam h.le) α μ (1 + 1) = μ from geo_of_le _ (by omega)] at this
  have hQαμ : Qv (puAmalgam h.le) α ≤ stab _ μ :=
    (qv_le_qv _ h20 hα hαβ).trans (qv_le_stab_of_adj _ hβμ)
  have hQμα : Qv (puAmalgam h.le) μ ≤ stab _ α :=
    (qv_le_qv _ h20 hμM hβμ.symm).trans (qv_le_stab_of_adj _ hαβ.symm)
  have hZμ : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ ZM (puAmalgam h.le) μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQαμ.trans (stab_le_normalizer_zm _ μ))
  have hZμs : ZM (puAmalgam h.le) μ ≤ stab _ α := by
    have := zv_le_vv h (α := α) (ρ := μ) hdμ.le
    rw [zv_of_isMVtx _ hμM] at this
    exact this.trans ((vv_le_qv h hb hα).trans (qv_le_stab _ α))
  have hQ : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Qv (puAmalgam h.le) α := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hZμs.trans (stab_le_normalizer_qv _ α))
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hα
  have hYU : ¬ Qv (puAmalgam h.le) μ ≤
      Subgroup.centralizer (Uloc h.le L α : Set (puAmalgam h.le).Universal) := by
    intro hle
    apply hH
    have h1 : Qv (puAmalgam h.le) μ ≤ Qv (puAmalgam h.le) α :=
      (le_inf hQμα hle).trans (S46.stab_inf_centralizer_uloc_le_qv h hφ hα)
    have h2 : Qv (puAmalgam h.le) μ = Qv (puAmalgam h.le) α := by
      obtain ⟨g, hg⟩ := exists_eq_smul_baseA _ hα
      obtain ⟨g', hg'⟩ := exists_eq_smul_baseA _ hμM
      have hgμ : (g' * g⁻¹) • α = μ := by rw [hg, smul_smul, inv_mul_cancel_right, hg']
      have : Finite ↥(stab (puAmalgam h.le) α) := finite_stab h hα
      have : Finite ↥(Qv (puAmalgam h.le) α) :=
        Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_stab _ α))
      refine Subgroup.eq_of_le_of_card_ge h1 ?_
      rw [← hgμ, qv_smul, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    rw [← h2, (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      (zm_le_centralizer_qv _ h20 hμM)]
    exact bot_le
  intro w hw
  refine mem_uloc_sup_dloc h hfull hα hψs hψ (hQ hw) (fun l hl => ?_) hQμα (fun y hy => ?_)
    (hQαμ.trans (stab_le_normalizer_qv _ μ)) (S46.isPGroup_qv_of_isMVtx h hμM) hYU
  · have h1 := ((mem_bloc_iff h hb hα).mp (hB hw)).2 l hl
    rw [← commutatorElement_inv]
    exact (ZM (puAmalgam h.le) α).inv_mem h1
  · exact Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hμM (hZμ hw)) y hy

end UD

end CFSG.Quasithin.MS93.S4A.C441
