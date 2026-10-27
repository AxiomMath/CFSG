module

public import CFSG.Quasithin.MS93.S4L461A
public import CFSG.Quasithin.MS93.S34F461

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Dloc

variable (h : PUHyp M T L) (hU : IsSL3U M T L) (hC : CentHyp (puAmalgam h.le))
include h hU hC

theorem commutator_commutator_zm_eq_bot_flat (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hNα : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α)
    {ρ μ : Vtx (puAmalgam h.le)} (hαρ : (puAmalgam h.le).treeGraph.Adj α ρ)
    (hρμ : (puAmalgam h.le).treeGraph.Adj ρ μ) (hμα : μ ≠ α)
    (hnorm : ¬ ZM (puAmalgam h.le) α' ≤
      Subgroup.normalizer ((ZM _ μ ⊔ centerOf (Vv _ α) : Subgroup _) : Set _)) :
    ⁅⁅ZM (puAmalgam h.le) μ, Vv _ α⁆, ZM _ α'⁆ = ⊥ := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  set γ := geo (puAmalgam h.le) α α' 2 with hγdef
  set N := centerOf (Vv (puAmalgam h.le) α)
  have hγ : IsMVtx _ γ := isMVtx_geo_two' hb4 hc
  have hdαγ : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_geo_crit hb4 hc (by omega)
  have hdαμ : (puAmalgam h.le).treeGraph.dist α μ = 2 := dist_eq_two_of_adj_adj _ hαρ hρμ hμα.symm
  have hμM : IsMVtx (puAmalgam h.le) μ := by
    have h1 := (isMVtx_iff_of_adj _ hαρ).mp hc.1
    have h2 := isMVtx_iff_of_adj _ hρμ
    tauto
  have hZμV : ZM (puAmalgam h.le) μ ≤ Vv _ α := by
    have : Zv (puAmalgam h.le) μ ≤ Vv _ α := le_iSup₂_of_le (f := fun x (_ : x ∈
      {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist α x ≤ 2}) =>
        Zv (puAmalgam h.le) x) μ (show _ ≤ 2 by omega) le_rfl
    rwa [zv_of_isMVtx _ hμM] at this
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hNn := S34F.stab_le_normalizer_centerOf h α
  have hμγ : ¬ ZM (puAmalgam h.le) μ ≤ Qv _ γ := by
    intro hle
    apply hnorm
    have h1 : ⁅ZM (puAmalgam h.le) μ, ZM _ α'⁆ ≤ N :=
      (Subgroup.commutator_mono (le_inf hZμV hle) le_rfl).trans
        (S34F.commutator_vv_inf_qv_le_centerOf_flat h hU hC hb4 hc hNα)
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    refine S4A.commutator_sup_le_of (h1.trans le_sup_right) ?_ ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans hNn)).trans
        le_sup_right |>.trans' (by rw [Subgroup.commutator_comm])
    · exact le_sup_left.trans Subgroup.le_normalizer
    · exact le_sup_right.trans Subgroup.le_normalizer
  have hdγμ : (puAmalgam h.le).treeGraph.dist γ μ = 4 := by
    have htri := dist_triangle (puAmalgam h.le) γ α μ
    rw [tdist_comm _ γ α, hdαγ, hdαμ] at htri
    by_contra hne
    exact hμγ (zm_le_qv_of_dist_le_three hb4 hμM (by rw [tdist_comm]; omega))
  have hcμ : IsCritical (puAmalgam h.le) μ γ :=
    ⟨hμM, by rw [tdist_comm, hdγμ, hb4], hμγ⟩
  have hcγ := ms22_iii _ h20 hb0 hC hcμ
  have hgeoρ : geo (puAmalgam h.le) μ γ 1 = ρ := by
    symm
    refine eq_geo_one _ hρμ.symm ?_
    have h1 := dist_triangle (puAmalgam h.le) ρ α γ
    have h2 := dist_triangle (puAmalgam h.le) μ ρ γ
    rw [tdist_comm _ ρ α, dist_eq_one_of_adj _ hαρ, hdαγ] at h1
    rw [dist_eq_one_of_adj _ hρμ.symm, tdist_comm _ μ γ, hdγμ] at h2
    rw [tdist_comm _ μ γ, hdγμ]
    omega
  have hNγ' := not_centerOf_le_bloc_of_smul h hc.1 hγ hNα
  have h4 := S34F.commutator_zm_flat_le_centerOf h hU hC hb4 hcγ hNγ'
  rw [show geo (puAmalgam h.le) μ γ 1 = ρ from hgeoρ] at h4
  have hVρ : Vv (puAmalgam h.le) α ≤ Qv _ ρ ⊓ S34F.flat h μ :=
    le_inf ((vv_le_qv h hb hc.1).trans (qv_le_qv _ h20 hc.1 hαρ))
      (vv_le_flat_of_dist_two h hU hb4 hc.1 hdαμ)
  have h5 : ⁅ZM (puAmalgam h.le) μ, Vv _ α⁆ ≤ centerOf (Vv _ γ) :=
    (Subgroup.commutator_mono le_rfl hVρ).trans h4
  have hZα'V : ZM (puAmalgam h.le) α' ≤ Vv _ γ := by
    have hα' := hc.isMVtx_right _ h20
    have : Zv (puAmalgam h.le) α' ≤ Vv _ γ := le_iSup₂_of_le (f := fun x (_ : x ∈
      {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist γ x ≤ 2}) =>
        Zv (puAmalgam h.le) x) α' (show _ ≤ 2 by rw [dist_geo_crit_right hb4 hc (by omega)])
        le_rfl
    rwa [zv_of_isMVtx _ hα'] at this
  rw [← le_bot_iff]
  refine (Subgroup.commutator_mono h5 hZα'V).trans ?_
  rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact inf_le_right

theorem commutator_vv_le_dloc_of_not_flat (hb4 : critDist (puAmalgam h.le) = 4)
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hNα : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α) :
    ⁅Vv (puAmalgam h.le) α, Vv _ α⁆ ≤ Dloc h.le L α := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h20 hα
  set β := geo (puAmalgam h.le) α α' 1 with hβdef
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hc
  set N := centerOf (Vv (puAmalgam h.le) α) with hNdef
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hVn := stab_le_normalizer_vv h α
  have hNn := S34F.stab_le_normalizer_centerOf h α
  have hDn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Dloc h.le L α : Set _) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hZβ : ZM (puAmalgam h.le) α' ≤ Qv _ β := zm_le_qv_geo_one _ h20 hb0 hc
  have hZQ : ¬ ZM (puAmalgam h.le) α' ≤ Qv _ α := (ms22_iii _ h20 hb0 hC hc).2.2
  have hZV : ∀ μ, (puAmalgam h.le).treeGraph.Adj β μ → ZM (puAmalgam h.le) μ ≤ Vv _ α := by
    intro μ hβμ
    by_cases hμα : μ = α
    · rw [hμα]; exact zm_le_vv h hα
    · have hμM : IsMVtx (puAmalgam h.le) μ := by
        have h1 := (isMVtx_iff_of_adj _ hαβ).mp hα
        have h2 := isMVtx_iff_of_adj _ hβμ
        tauto
      have : Zv (puAmalgam h.le) μ ≤ Vv _ α := le_iSup₂_of_le (f := fun x (_ : x ∈
        {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist α x ≤ 2}) =>
          Zv (puAmalgam h.le) x) μ
          (show _ ≤ 2 by rw [dist_eq_two_of_adj_adj _ hαβ hβμ (Ne.symm hμα)]) le_rfl
      rwa [zv_of_isMVtx _ hμM] at this
  by_contra hD
  obtain ⟨μ, hβμ, hμ⟩ : ∃ μ, (puAmalgam h.le).treeGraph.Adj β μ ∧
      ¬ ⁅ZM (puAmalgam h.le) μ, Vv _ α⁆ ≤ Dloc h.le L α := by
    by_contra hno
    apply hD
    have hall : ∀ ρ, (puAmalgam h.le).treeGraph.Adj α ρ → ∀ μ',
        (puAmalgam h.le).treeGraph.Adj ρ μ' → ⁅ZM (puAmalgam h.le) μ', Vv _ α⁆ ≤ Dloc h.le L α := by
      intro ρ hρ μ' hμ'
      obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hαβ hρ
      have hμ0 : (puAmalgam h.le).treeGraph.Adj β (g⁻¹ • μ') := by
        have := (adj_smul _ g⁻¹ ρ μ').mpr hμ'
        rwa [← hgρ, inv_smul_smul] at this
      have h1 : ⁅ZM (puAmalgam h.le) (g⁻¹ • μ'), Vv _ α⁆ ≤ Dloc h.le L α := by
        by_contra h'
        exact hno ⟨_, hμ0, h'⟩
      have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
      rwa [Subgroup.map_commutator, ← zm_smul, smul_inv_smul,
        map_conj_eq_of_mem_normalizer (hVn hg), map_conj_eq_of_mem_normalizer (hDn hg)] at h2
    have hVD : Vv (puAmalgam h.le) α ≤ Subgroup.normalizer (Dloc h.le L α : Set _) :=
      hVs.trans hDn
    have hsub : Vv (puAmalgam h.le) α ≤ vvPerp (X := puAmalgam h.le) α (Dloc h.le L α) := by
      rw [vv_eq_iSup_vv hα]
      refine iSup₂_le fun ρ hρ => ?_
      have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
      rw [vv_eq_iSup_of_not_isMVtx hρH]
      refine iSup₂_le fun μ' hμ' => fun z hz => ?_
      rw [mem_vvPerp_iff hVD]
      have hμ'V : ZM (puAmalgam h.le) μ' ≤ Vv _ α := by
        rw [vv_eq_iSup_vv hα]
        exact (zm_le_vv_of_adj hμ' (by have := isMVtx_iff_of_adj _ hμ'; tauto)).trans
          (le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α) =>
            Vv (puAmalgam h.le) ρ) ρ hρ le_rfl)
      exact ⟨hμ'V hz, fun w hw => hall ρ hρ μ' hμ' (Subgroup.commutator_mem_commutator hz hw)⟩
    rw [Subgroup.commutator_le]
    intro v hv w hw
    exact ((mem_vvPerp_iff hVD).mp (hsub hv)).2 w hw
  have hμα : μ ≠ α := by
    rintro rfl
    apply hμ
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le (vv_le_qv h hb hα)))]
    exact bot_le
  set X₁ := ZM (puAmalgam h.le) μ ⊔ N with hX₁
  set X₂ := ⁅ZM (puAmalgam h.le) μ, Vv _ α⁆ with hX₂
  have hβs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hβμs : Qv (puAmalgam h.le) β ≤ stab _ μ := qv_le_stab_of_adj _ hβμ
  have hTX₁ : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer (X₁ : Set _) :=
    (le_inf (hβμs.trans (stab_le_normalizer_zm _ μ)) (hβs.trans hNn)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hTX₂ : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer (X₂ : Set _) := by
    refine le_normalizer_of_map_conj_le fun t ht => ?_
    rw [hX₂, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
      (hβμs.trans (stab_le_normalizer_zm _ μ) ht), map_conj_eq_of_mem_normalizer (hVn (hβs ht))]
  have hgen : stab (puAmalgam h.le) α =
      (⨆ g ∈ stab (puAmalgam h.le) α, (ZM _ α').map (MulAut.conj g).toMonoidHom) ⊔
        Qv _ β := by
    have hcl : conjCl (stab (puAmalgam h.le) α) (ZM _ α') =
        ⨆ g ∈ stab (puAmalgam h.le) α, (ZM _ α').map (MulAut.conj g).toMonoidHom := rfl
    rw [← hcl]
    apply le_antisymm
    · calc stab (puAmalgam h.le) α = Ltil h.le L α ⊔ Qv _ β :=
            S34F.stab_eq_ltil_sup_qv_gen h hα hαβ
        _ ≤ conjCl (stab (puAmalgam h.le) α) (ZM _ α') ⊔ Qv _ β :=
            sup_le_sup_right (S34F.ltil_le_of_normal_gen h hα hαβ (conjCl_le_of_le hZs)
              (le_normalizer_conjCl _ _) (le_conjCl _ _) hZβ hZQ) _
    · exact sup_le (conjCl_le_of_le hZs) hβs
  have hX₁g : ∀ g ∈ stab (puAmalgam h.le) α,
      X₁.map (MulAut.conj g).toMonoidHom = ZM (puAmalgam h.le) (g • μ) ⊔ N := by
    intro g hg
    rw [hX₁, Subgroup.map_sup, ← zm_smul, map_conj_eq_of_mem_normalizer (hNn hg)]
  have hX₂g : ∀ g ∈ stab (puAmalgam h.le) α,
      X₂.map (MulAut.conj g).toMonoidHom = ⁅ZM (puAmalgam h.le) (g • μ), Vv _ α⁆ := by
    intro g hg
    rw [hX₂, Subgroup.map_commutator, ← zm_smul, map_conj_eq_of_mem_normalizer (hVn hg)]
  have hcore : ∀ g ∈ stab (puAmalgam h.le) α,
      ¬ ZM (puAmalgam h.le) α' ≤ Subgroup.normalizer ((X₁.map (MulAut.conj g).toMonoidHom :
        Subgroup _) : Set _) → ⁅X₂.map (MulAut.conj g).toMonoidHom, ZM _ α'⁆ = ⊥ := by
    intro g hg hng
    rw [hX₁g g hg] at hng
    rw [hX₂g g hg]
    have hgβ : (puAmalgam h.le).treeGraph.Adj α (g • β) := by
      have := (adj_smul _ g α β).mpr hαβ
      rwa [(mem_stab _).mp hg] at this
    have hgμ : (puAmalgam h.le).treeGraph.Adj (g • β) (g • μ) := (adj_smul _ g β μ).mpr hβμ
    have hgμα : g • μ ≠ α := by
      intro he
      apply hμα
      have : g • μ = g • α := by rw [he, (mem_stab _).mp hg]
      exact smul_left_cancel g this
    exact commutator_commutator_zm_eq_bot_flat h hU hC hb4 hc hNα hgβ hgμ hgμα hng
  by_cases hX₁n : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (X₁ : Set _)
  ·
    apply hμ
    suffices hcen : ZM (puAmalgam h.le) μ ≤ Subgroup.centralizer (Vv _ α : Set _) by
      rw [hX₂, (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hcen]
      exact bot_le
    rw [vv_eq_iSup_vv hα]
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun ρ hρ => ?_
    rw [← Subgroup.le_centralizer_iff]
    obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hαβ hρ
    have hgμ : (puAmalgam h.le).treeGraph.Adj ρ (g • μ) := by
      rw [← hgρ]; exact (adj_smul _ g β μ).mpr hβμ
    have hgμM : IsMVtx (puAmalgam h.le) (g • μ) := by
      have h1 := (isMVtx_iff_of_adj _ hρ).mp hα
      have h2 := isMVtx_iff_of_adj _ hgμ
      tauto
    have h1 : ZM (puAmalgam h.le) μ ≤ Vv _ ρ ⊔ N := by
      have h0 : ZM (puAmalgam h.le) μ ≤ X₁.map (MulAut.conj g).toMonoidHom := by
        rw [map_conj_eq_of_mem_normalizer (hX₁n hg)]; exact le_sup_left
      rw [hX₁g g hg] at h0
      exact h0.trans (sup_le_sup_right (zm_le_vv_of_adj hgμ hgμM) _)
    have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
    have hVρab := vv_le_centralizer_of_not_isMVtx h20 hb hρH
    have hVρα : Vv (puAmalgam h.le) ρ ≤ Vv _ α := by
      rw [vv_eq_iSup_vv hα]
      exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α) =>
        Vv (puAmalgam h.le) ρ) ρ hρ le_rfl
    refine h1.trans (sup_le ?_ ?_)
    · exact (Subgroup.le_centralizer_iff.mp hVρab)
    · exact inf_le_right.trans (Subgroup.centralizer_le hVρα)
  · by_cases hX₂n : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (X₂ : Set _)
    · obtain ⟨g, hg, hng, -⟩ := ms21_vii _ hgen hTX₁ hX₁n hTX₁ hX₁n
      have hc0 := hcore g hg hng
      rw [map_conj_eq_of_mem_normalizer (hX₂n hg)] at hc0
      apply hμ
      have hL := S34F.commutator_ltil_le_of_commutator_le_gen h hα hαβ (A := X₂) (B := ⊥) hX₂n
        (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge) hc0.le hZβ hZQ
      have hX₂Q : X₂ ≤ Qv (puAmalgam h.le) α := by
        rw [hX₂, Subgroup.commutator_comm]
        exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
          (((hZV μ hβμ).trans hVs).trans hVn)).trans (vv_le_qv h hb hα)
      exact le_dloc_of_commutator_le h hα hX₂Q (hL.trans bot_le)
    · obtain ⟨g, hg, hng, hng₂⟩ := ms21_vii _ hgen hTX₁ hX₁n hTX₂ hX₂n
      apply hng₂
      exact le_normalizer_of_le_centralizer (by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact hcore g hg hng)

end Dloc

end CFSG.Quasithin.MS93.S4L
