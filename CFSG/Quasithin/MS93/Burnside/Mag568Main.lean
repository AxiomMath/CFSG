module

public import CFSG.Quasithin.MS93.Burnside.Mag568P16
public import CFSG.Quasithin.MS93.Burnside.Mag568P17
public import CFSG.Quasithin.MS93.Burnside.Mag568RG
public import CFSG.Quasithin.MS93.Burnside.SL3GMin
public import CFSG.Quasithin.MS93.S4XKey

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F
open scoped commutatorElement

section Conj

variable {Γ : Type*} [Group Γ]

theorem burnsideMag568_map_conj_map_conj (H : Subgroup Γ) (a b : Γ) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem burnsideMag568_map_conj_centralizer (E : Subgroup Γ) (k : Γ) :
    (Subgroup.centralizer (E : Set Γ)).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ((E.map (MulAut.conj k).toMonoidHom : Subgroup Γ) : Set Γ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hy e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * e * k⁻¹ * (k * y * k⁻¹) = k * (e * y) * k⁻¹ := by group
      _ = k * (y * e) * k⁻¹ := by rw [this]
      _ = k * y * k⁻¹ * (k * e * k⁻¹) := by group
  · intro hx
    refine ⟨k⁻¹ * x * k, Subgroup.mem_centralizer_iff.mpr fun e he => ?_, by simp [mul_assoc]⟩
    have := Subgroup.mem_centralizer_iff.mp hx (k * e * k⁻¹) ⟨e, he, rfl⟩
    calc e * (k⁻¹ * x * k) = k⁻¹ * ((k * e * k⁻¹) * x) * k := by group
      _ = k⁻¹ * (x * (k * e * k⁻¹)) * k := by rw [this]
      _ = k⁻¹ * x * k * e := by group

end Conj

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideMag568_zE_eq (h : PUHyp M T L) (E : Subgroup (puAmalgam h.le).Universal)
    (k : (puAmalgam h.le).Universal) :
    mag568_zE h E k = Uloc h.le L (k • baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer ((E.map (MulAut.conj k).toMonoidHom :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
  rw [burnsideMag568_zE_def, Subgroup.map_inf _ _ _ (MulAut.conj k).injective,
    burnsideMag568_map_conj_centralizer]
  congr 1
  exact (puTrans_smul h.le (S4A.Uq_normal h) k _).symm

theorem burnsideMag568_zE_le_uloc (h : PUHyp M T L) (E : Subgroup (puAmalgam h.le).Universal)
    (k : (puAmalgam h.le).Universal) :
    mag568_zE h E k ≤ Uloc h.le L (k • baseA (puAmalgam h.le)) :=
  (burnsideMag568_zE_eq h E k).le.trans inf_le_left

theorem burnsideMag568_qv_le_normalizer_zE (h : PUHyp M T L)
    {E : Subgroup (puAmalgam h.le).Universal}
    (hET : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (E : Set (puAmalgam h.le).Universal))
    (k : (puAmalgam h.le).Universal) :
    Qv (puAmalgam h.le) (k • baseB _) ≤
      Subgroup.normalizer (mag568_zE h E k : Set (puAmalgam h.le).Universal) := by
  have hβU : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (Uloc h.le L (baseA (puAmalgam h.le)) : Set _) :=
    (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm).trans (S4A.stab_le_normalizer_uloc h _)
  have hZ₀T := burnsideSL3G_le_normalizer_inf_centralizer hβU hET
  rw [qv_smul]
  rintro _ ⟨y, hy, rfl⟩
  rw [burnsideMag568_zE_def]
  exact mag568_conj_mem_normalizer_map k (hZ₀T hy)

theorem burnsideMag568_isLine_zE (h : PUHyp M T L) (hU : IsSL3U M T L)
    {E : Subgroup (puAmalgam h.le).Universal} (hEf : E ≤ S34F.flat h (baseA _))
    (hcard : Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) ^ 3 =
      Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le))))
    (k : (puAmalgam h.le).Universal) :
    mag568_IsLine h (k • baseA _) (mag568_zE h E k) := by
  rw [burnsideMag568_zE_eq h E k]
  refine burnsideMag568_isLine h hU ((isMVtx_smul _ k _).mpr (PU.isMVtx_baseA _)) ?_ ?_
  · rw [S34F.flat, puTrans_smul h.le (flat_subgroupOf_normal h)]
    exact Subgroup.map_mono hEf
  · rw [← burnsideMag568_zE_eq h E k, burnsideMag568_zE_def,
      Subgroup.card_map_of_injective (MulAut.conj k).injective,
      show Uloc h.le L (k • baseA (puAmalgam h.le)) =
        (Uloc h.le L (baseA (puAmalgam h.le))).map (MulAut.conj k).toMonoidHom from
          puTrans_smul h.le (S4A.Uq_normal h) k _,
      Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hcard

theorem burnsideMag568_commutator_qv_ne_bot (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {α δ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hδ : IsMVtx _ δ) (hd : (puAmalgam h.le).treeGraph.dist α δ = 2)
    {Z : Subgroup (puAmalgam h.le).Universal} (hZ : Z ≤ Uloc h.le L δ)
    (hne : ¬ ⁅Z, Ltil h.le L α⁆ ≤ ZM _ α) : ⁅Z, Qv (puAmalgam h.le) α⁆ ≠ ⊥ := by
  intro hbot
  apply hne
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hZZ : Z ≤ ZM _ δ := hZ.trans (S34F.uloc_le_zm' h hδ)
  have hZQ : Z ≤ Qv _ α :=
    hZZ.trans (zm_le_qv_of_dist_lt _ hδ (by rw [tdist_comm, hd]; omega))
  have hZC : Z ≤ Subgroup.centralizer (Qv (puAmalgam h.le) α : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hZX : Z ≤ XM _ α := by
    intro z hz
    have hz2 : z ^ 2 = 1 := (isElemAbelian_zm _ h20 hb0 hδ).2 z (hZZ hz)
    exact Subgroup.subset_closure ⟨⟨hZQ hz, hZC hz⟩, hz2⟩
  rw [xm_eq_uloc_sup_zloc_of_isSL3U h hU hα] at hZX
  have hZD : Z ≤ Dloc h.le L α ⊔ Uloc h.le L α :=
    hZX.trans (sup_comm (Uloc h.le L α) (Zloc h.le L α) ▸ sup_le_sup_right (zloc_le_dloc h α) _)
  have hDU : Dloc h.le L α ≤ Subgroup.centralizer (Uloc h.le L α : Set _) :=
    (dloc_le_qv h hα).trans ((Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα)).trans
      (Subgroup.centralizer_le (S34F.uloc_le_zm' h hα)))
  refine (Subgroup.commutator_mono hZD le_rfl).trans ?_
  rw [S34F.commutator_sup_eq_of_le_centralizer hDU (dloc_le_centralizer_ltil h hα)]
  exact (Subgroup.le_normalizer_iff_commutator_le_left.mp ((puTrans_le_stab h.le L α).trans
    (S4A.stab_le_normalizer_uloc h α))).trans (S34F.uloc_le_zm' h hα)

theorem burnsideMag568_hgen (h : PUHyp M T L) {α γ α' : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hαγ : (puAmalgam h.le).treeGraph.Adj α γ)
    (hc : IsCritical (puAmalgam h.le) α α') (hgeo : geo (puAmalgam h.le) α α' 1 = γ) :
    stab (puAmalgam h.le) α =
      (⨆ k ∈ stab (puAmalgam h.le) α, (ZM _ α').map (MulAut.conj k).toMonoidHom) ⊔
        Qv _ γ := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hZβ : ZM (puAmalgam h.le) α' ≤ Qv _ γ := hgeo ▸ zm_le_qv_geo_one _ h20 hb0 hc
  have hZQ : ¬ ZM (puAmalgam h.le) α' ≤ Qv _ α := (ms22_iii _ h20 hb0 h.centHyp hc).2.2
  have hβs : Qv (puAmalgam h.le) γ ≤ stab _ α := qv_le_stab_of_adj _ hαγ.symm
  have hcl : conjCl (stab (puAmalgam h.le) α) (ZM _ α') =
      ⨆ k ∈ stab (puAmalgam h.le) α, (ZM _ α').map (MulAut.conj k).toMonoidHom := rfl
  rw [← hcl]
  apply le_antisymm
  · calc stab (puAmalgam h.le) α = Ltil h.le L α ⊔ Qv _ γ :=
          S34F.stab_eq_ltil_sup_qv_gen h hα hαγ
      _ ≤ conjCl (stab (puAmalgam h.le) α) (ZM _ α') ⊔ Qv _ γ :=
          sup_le_sup_right (S34F.ltil_le_of_normal_gen h hα hαγ (conjCl_le_of_le hZs)
            (le_normalizer_conjCl _ _) (le_conjCl _ _) hZβ hZQ) _
  · exact sup_le (conjCl_le_of_le hZs) hβs

theorem burnsideMag568_le_commutator_qv_zE (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hbad : mag568_Bad h)
    {E : Subgroup (puAmalgam h.le).Universal} (hEf : E ≤ S34F.flat h (baseA _))
    (hET : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (E : Set (puAmalgam h.le).Universal))
    (hcard : Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) ^ 3 =
      Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le))))
    (hRG : mag568_RG h (Uloc h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)))
    (k : (puAmalgam h.le).Universal) {α₁ : Vtx (puAmalgam h.le)}
    (hk : (puAmalgam h.le).treeGraph.Adj (k • baseB _) α₁)
    (hne : ⁅mag568_zE h E k, Qv (puAmalgam h.le) α₁⁆ ≠ ⊥) :
    mag568_zE h E k ≤ ⁅Uloc h.le L (k • baseA _), Qv (puAmalgam h.le) α₁⁆ := by
  have hβU : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (Uloc h.le L (baseA (puAmalgam h.le)) : Set _) :=
    (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm).trans (S4A.stab_le_normalizer_uloc h _)
  have hZ₀T := burnsideSL3G_le_normalizer_inf_centralizer hβU hET
  have hk' : (puAmalgam h.le).treeGraph.Adj (baseB _) (k⁻¹ • α₁) := by
    have := (adj_smul _ k⁻¹ (k • baseB _) α₁).mpr hk
    rwa [inv_smul_smul] at this
  have hQ : Qv (puAmalgam h.le) α₁ =
      (Qv (puAmalgam h.le) (k⁻¹ • α₁)).map (MulAut.conj k).toMonoidHom := by
    rw [← qv_smul, smul_inv_smul]
  have hU' : Uloc h.le L (k • baseA (puAmalgam h.le)) =
      (Uloc h.le L (baseA (puAmalgam h.le))).map (MulAut.conj k).toMonoidHom :=
    puTrans_smul h.le (S4A.Uq_normal h) _ _
  rw [hQ, burnsideMag568_zE_def, ← Subgroup.map_commutator] at hne
  rw [hQ, hU', burnsideMag568_zE_def, ← Subgroup.map_commutator]
  refine Subgroup.map_mono
    (burnsideMag568_le_commutator_qv h hU hb hbad hEf hcard hZ₀T hRG hk' ?_)
  intro hbot
  apply hne
  rw [hbot, Subgroup.map_bot]

theorem burnsideMag568_false_of_config (h : PUHyp M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hU : IsSL3U M T L) (hbad : mag568_Bad h)
    {E : Subgroup (puAmalgam h.le).Universal} (hEf : E ≤ S34F.flat h (baseA _))
    (hET : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (E : Set (puAmalgam h.le).Universal))
    (hcard : Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) ^ 3 =
      Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le))))
    (hRG : mag568_RG h (Uloc h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)))
    {α α' : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hc : IsCritical (puAmalgam h.le) α α')
    (g₂ : (puAmalgam h.le).Universal) {γ₂ δ₂ : Vtx (puAmalgam h.le)}
    (hγ₂ : g₂ • baseB (puAmalgam h.le) = γ₂) (hδ₂ : g₂ • baseA (puAmalgam h.le) = δ₂)
    (hαγ₂ : (puAmalgam h.le).treeGraph.Adj α γ₂) (hδ₂α : δ₂ ≠ α)
    (hne₂ : ¬ ⁅mag568_zE h E g₂, Ltil h.le L α⁆ ≤ ZM _ α)
    (hn₁ : ¬ ZM (puAmalgam h.le) α' ≤ Subgroup.normalizer
      ((ZM (puAmalgam h.le) δ₂ ⊔ ZM _ α : Subgroup (puAmalgam h.le).Universal) :
        Set (puAmalgam h.le).Universal))
    (hn₂ : ¬ ZM (puAmalgam h.le) α' ≤ Subgroup.normalizer
      ((mag568_zE h E g₂ ⊔ ZM _ α : Subgroup (puAmalgam h.le).Universal) :
        Set (puAmalgam h.le).Universal)) : False := by
  have h20 := h.hyp20
  have hC := h.centHyp
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hα₀ := PU.isMVtx_baseA (puAmalgam h.le)
  have hline₀ : mag568_IsLine h (baseA _) (Uloc h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) :=
    burnsideMag568_isLine h hU hα₀ hEf hcard
  have hγ₂δ₂ : (puAmalgam h.le).treeGraph.Adj γ₂ δ₂ := by
    rw [← hγ₂, ← hδ₂]
    exact (adj_smul _ g₂ _ _).mpr (adj_baseA_baseB _).symm
  have hδ₂M : IsMVtx _ δ₂ := hδ₂ ▸ (isMVtx_smul _ g₂ _).mpr hα₀
  have hZ₂U : mag568_zE h E g₂ ≤ Uloc h.le L δ₂ := hδ₂ ▸ burnsideMag568_zE_le_uloc h E g₂
  have hZ₂n : Qv (puAmalgam h.le) γ₂ ≤
      Subgroup.normalizer (mag568_zE h E g₂ : Set (puAmalgam h.le).Universal) :=
    hγ₂ ▸ burnsideMag568_qv_le_normalizer_zE h hET g₂
  have hZ₂line : mag568_IsLine h δ₂ (mag568_zE h E g₂) :=
    hδ₂ ▸ burnsideMag568_isLine_zE h hU hEf hcard g₂
  have hγ₂ne : γ₂ ≠ geo _ α α' 1 := fun he =>
    hn₂ (mag568_gamma_ne_geo_one h hU hb2 hEf hET hline₀ hc (hγ₂.trans he) (hδ₂.trans_ne hδ₂α))
  have hdαδ₂ : (puAmalgam h.le).treeGraph.dist α δ₂ = 2 :=
    dist_eq_two_of_adj_adj _ hαγ₂ hγ₂δ₂ hδ₂α.symm
  have hdαα' : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hdγ₂α' : (puAmalgam h.le).treeGraph.dist γ₂ α' = critDist (puAmalgam h.le) + 1 := by
    rcases dist_adj_cases _ hαγ₂ α' with h1 | h1
    · rw [tdist_comm, h1, tdist_comm, hdαα']
    · exfalso
      exact hγ₂ne (eq_geo_one _ hαγ₂ (by rw [tdist_comm _ γ₂ α', tdist_comm _ α α']; omega))
  have hdδ₂α' : (puAmalgam h.le).treeGraph.dist δ₂ α' = critDist (puAmalgam h.le) + 2 := by
    rcases dist_adj_cases _ hγ₂δ₂ α' with h1 | h1
    · rw [tdist_comm, h1, tdist_comm, hdγ₂α']
    · exfalso
      have e1 : δ₂ = geo (puAmalgam h.le) γ₂ α' 1 :=
        eq_geo_one _ hγ₂δ₂ (by rw [tdist_comm _ δ₂ α', tdist_comm _ γ₂ α']; omega)
      have e2 : α = geo (puAmalgam h.le) γ₂ α' 1 :=
        eq_geo_one _ hαγ₂.symm (by rw [hdαα', hdγ₂α'])
      exact hδ₂α (e1.trans e2.symm)
  have hZ₂Q : ⁅mag568_zE h E g₂, Qv (puAmalgam h.le) α⁆ ≠ ⊥ :=
    burnsideMag568_commutator_qv_ne_bot h hU hb2 hα hδ₂M hdαδ₂ hZ₂U hne₂
  have hZα'Zα : ZM (puAmalgam h.le) α' ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    (zm_le_stab_of_isCritical _ h20 hb0 hc).trans (stab_le_normalizer_zm _ α)
  have hZ₂α' : ¬ ⁅mag568_zE h E g₂, ZM (puAmalgam h.le) α'⁆ ≤ ZM _ α := fun hle =>
    hn₂ (burnsideSL3G_le_normalizer_of_commutator_le hZα'Zα (hle.trans le_sup_right))
  by_cases hcr : ZM (puAmalgam h.le) δ₂ ≤ Qv _ (geo (puAmalgam h.le) α' α 2)
  ·
    have h16 : mag568_zE h E g₂ ≤ ⁅Uloc h.le L δ₂, Qv (puAmalgam h.le) α⁆ := by
      rw [← hδ₂]
      exact burnsideMag568_le_commutator_qv_zE h hU hb2 hbad hEf hET hcard hRG g₂
        (hγ₂ ▸ hαγ₂.symm) hZ₂Q
    have hZ₂B : mag568_zE h E g₂ ≤ ⁅ZM (puAmalgam h.le) δ₂, Qv (puAmalgam h.le) α⁆ :=
      h16.trans (Subgroup.commutator_mono (S34F.uloc_le_zm' h hδ₂M) le_rfl)
    have hB : ¬ ⁅⁅ZM (puAmalgam h.le) δ₂, Qv (puAmalgam h.le) α⁆,
        ZM (puAmalgam h.le) α'⁆ ≤ ZM _ α :=
      fun hle => hZ₂α' ((Subgroup.commutator_mono hZ₂B le_rfl).trans hle)
    have h17 := burnsideMag568_commutator_le_of_flat_plane h hU hb hbad hc hdαδ₂ hcr hB
    have hZδ₂Q : ZM (puAmalgam h.le) δ₂ ≤ Qv _ α :=
      zm_le_qv_of_dist_lt _ hδ₂M (by rw [tdist_comm, hdαδ₂]; omega)
    exact hn₁ (ms21_vi _ h20 hb0 hc hdαδ₂ hZδ₂Q h17).1
  ·
    have hc' := ms22_iii _ h20 hb0 hC hc
    have hdα'α : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := hc'.2.1
    obtain ⟨ν, hνdef⟩ : ∃ ν, ν = geo (puAmalgam h.le) α' α 2 := ⟨_, rfl⟩
    rw [← hνdef] at hcr
    have hν1 : (puAmalgam h.le).treeGraph.dist α' ν = 2 := hνdef ▸ dist_geo _ (by omega)
    have hν2 : (puAmalgam h.le).treeGraph.dist ν α = critDist (puAmalgam h.le) - 2 := by
      rw [hνdef, dist_geo_right _ (by omega), hdα'α]
    have hdδ₂ν : (puAmalgam h.le).treeGraph.dist δ₂ ν = critDist (puAmalgam h.le) := by
      have h1 := dist_triangle _ δ₂ α ν
      have h2 := dist_triangle _ δ₂ ν α'
      rw [tdist_comm _ α ν, hν2, tdist_comm _ δ₂ α, hdαδ₂] at h1
      rw [tdist_comm _ ν α', hν1, hdδ₂α'] at h2
      omega
    have hcδ : IsCritical (puAmalgam h.le) δ₂ ν := ⟨hδ₂M, hdδ₂ν, hcr⟩
    have hgeoδ₂ : geo (puAmalgam h.le) δ₂ α 1 = γ₂ := by
      refine (eq_geo_one _ hγ₂δ₂.symm ?_).symm
      rw [dist_eq_one_of_adj _ hαγ₂.symm, tdist_comm _ δ₂ α, hdαδ₂]
    have hZn : Qv (puAmalgam h.le) (geo _ δ₂ α 1) ≤
        Subgroup.normalizer (mag568_zE h E g₂ : Set (puAmalgam h.le).Universal) := by
      rw [hgeoδ₂]
      exact hZ₂n
    have hP2 := mag568_le_qv_alpha'_sub_two h hU hC hb hc hdαδ₂ hdδ₂α' hZ₂line hZn
    have hcδ' : IsCritical (puAmalgam h.le) δ₂ (geo (puAmalgam h.le) α' α 2) := hνdef ▸ hcδ
    have hP6 := mag568_false_of_crit_delta h hU hC hb hbad hc hdαδ₂ hdδ₂α' hcδ'
      (le_inf hZ₂U hP2)
    exact hZ₂α' (by rw [hP6]; exact bot_le)

theorem burnsideMag568_commutator_zE_ltil_le (h : PUHyp M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hU : IsSL3U M T L) (hbad : mag568_Bad h)
    {E : Subgroup (puAmalgam h.le).Universal} (hEf : E ≤ S34F.flat h (baseA _))
    (hET : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (E : Set (puAmalgam h.le).Universal))
    (hcard : Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) ^ 3 =
      Nat.card ↥(Uloc h.le L (baseA (puAmalgam h.le))))
    (hRG : mag568_RG h (Uloc h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)))
    (g : (puAmalgam h.le).Universal) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hgα : (puAmalgam h.le).treeGraph.Adj (g • baseB _) α) :
    ⁅mag568_zE h E g, Ltil h.le L α⁆ ≤ ZM _ α := by
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hα₀β := adj_baseA_baseB (puAmalgam h.le)
  by_contra hne
  have hαγ : (puAmalgam h.le).treeGraph.Adj α (g • baseB _) := hgα.symm
  have hγδ : (puAmalgam h.le).treeGraph.Adj (g • baseB _) (g • baseA _) :=
    (adj_smul _ g _ _).mpr hα₀β.symm
  have hδM : IsMVtx _ (g • baseA (puAmalgam h.le)) :=
    (isMVtx_smul _ g _).mpr (PU.isMVtx_baseA _)
  have hZZδ : mag568_zE h E g ≤ ZM _ (g • baseA _) :=
    (burnsideMag568_zE_le_uloc h E g).trans (S34F.uloc_le_zm' h hδM)
  have hδα : g • baseA (puAmalgam h.le) ≠ α := by
    intro he
    apply hne
    have hZα : mag568_zE h E g ≤ ZM _ α := he ▸ hZZδ
    exact (Subgroup.commutator_mono hZα le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((puTrans_le_stab h.le L α).trans (stab_le_normalizer_zm _ α)))
  have hdαδ : (puAmalgam h.le).treeGraph.dist α (g • baseA _) = 2 :=
    dist_eq_two_of_adj_adj _ hαγ hγδ hδα.symm
  have hZQ : ⁅mag568_zE h E g, Qv (puAmalgam h.le) α⁆ ≠ ⊥ :=
    burnsideMag568_commutator_qv_ne_bot h hU hb2 hα hδM hdαδ (burnsideMag568_zE_le_uloc h E g) hne
  obtain ⟨α', hc, hgeo⟩ := burnsideSL3G_exists_isCritical_geo h hα hαγ
  have hgen := burnsideMag568_hgen h hα hαγ hc hgeo
  have hγs : Qv (puAmalgam h.le) (g • baseB _) ≤ stab _ α := qv_le_stab_of_adj _ hαγ.symm
  have hγsδ : Qv (puAmalgam h.le) (g • baseB _) ≤ stab _ (g • baseA _) :=
    qv_le_stab_of_adj _ hγδ
  have h₁ : Qv (puAmalgam h.le) (g • baseB _) ≤ Subgroup.normalizer
      ((ZM (puAmalgam h.le) (g • baseA _) ⊔ ZM _ α : Subgroup (puAmalgam h.le).Universal) :
        Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (hγsδ.trans (stab_le_normalizer_zm _ _))
      (hγs.trans (stab_le_normalizer_zm _ α))
  have h₂ : Qv (puAmalgam h.le) (g • baseB _) ≤ Subgroup.normalizer
      ((mag568_zE h E g ⊔ ZM _ α : Subgroup (puAmalgam h.le).Universal) :
        Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (burnsideMag568_qv_le_normalizer_zE h hET g)
      (hγs.trans (stab_le_normalizer_zm _ α))
  have h₁' : ¬ stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((ZM (puAmalgam h.le) (g • baseA _) ⊔ ZM _ α : Subgroup (puAmalgam h.le).Universal) :
        Set (puAmalgam h.le).Universal) := by
    intro hn
    rcases mag568_not_normal_sup h hα hδM hαγ hγδ le_rfl hn with h1 | h1
    · exact hne ((Subgroup.commutator_mono hZZδ le_rfl).trans h1)
    · apply hZQ
      rw [eq_bot_iff, ← h1]
      exact Subgroup.commutator_mono hZZδ le_rfl
  have h₂' : ¬ stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((mag568_zE h E g ⊔ ZM _ α : Subgroup (puAmalgam h.le).Universal) :
        Set (puAmalgam h.le).Universal) := by
    intro hn
    rcases mag568_not_normal_sup h hα hδM hαγ hγδ hZZδ hn with h1 | h1
    · exact hne h1
    · exact hZQ h1
  obtain ⟨g', hg', hn₁, hn₂⟩ := ms21_vii _ hgen h₁ h₁' h₂ h₂'
  have hg'α : g' • α = α := (mem_stab _).mp hg'
  have hZαg : (ZM (puAmalgam h.le) α).map (MulAut.conj g').toMonoidHom = ZM _ α :=
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ α hg')
  have hZg : (mag568_zE h E g).map (MulAut.conj g').toMonoidHom = mag568_zE h E (g' * g) := by
    rw [burnsideMag568_zE_def, burnsideMag568_zE_def, burnsideMag568_map_conj_map_conj]
  rw [Subgroup.map_sup, hZαg, ← zm_smul, ← mul_smul] at hn₁
  rw [Subgroup.map_sup, hZαg, hZg] at hn₂
  have hαγ₂ : (puAmalgam h.le).treeGraph.Adj α ((g' * g) • baseB _) := by
    have := (adj_smul _ g' α (g • baseB _)).mpr hαγ
    rwa [hg'α, ← mul_smul] at this
  have hδ₂α : (g' * g) • baseA (puAmalgam h.le) ≠ α := by
    rw [mul_smul]
    intro he
    apply hδα
    have : g' • (g • baseA (puAmalgam h.le)) = g' • α := by rw [he, hg'α]
    exact smul_left_cancel g' this
  have hne₂ : ¬ ⁅mag568_zE h E (g' * g), Ltil h.le L α⁆ ≤ ZM _ α := by
    intro hle
    apply hne
    have hL : (Ltil h.le L α).map (MulAut.conj g').toMonoidHom = Ltil h.le L α :=
      map_conj_eq_of_mem_normalizer (stab_le_normalizer_puTrans h.le (S4A.L_normal h) α hg')
    rw [← hZg, ← hL, ← Subgroup.map_commutator, ← hZαg] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g').injective).mp hle
  exact burnsideMag568_false_of_config h hb hU hbad hEf hET hcard hRG hα hc (g' * g) rfl rfl
    hαγ₂ hδ₂α hne₂ hn₁ hn₂

theorem burnsideMag568_key_of_bad (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hU : IsSL3U M T L) (hbad : mag568_Bad h) :
    ∃ E : Subgroup (puAmalgam h.le).Universal, E ≤ S34F.flat h (baseA _) ∧
      Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≠ ⊥ ∧
      ∀ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
        ⁅Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal),
          Ltil h.le L δ⁆ ≤ ZM _ δ := by
  obtain ⟨E, hEf, hET, hne, hcard, hRG⟩ := burnsideMag568_rg_of_bad h hb hU hbad
  refine ⟨E, hEf, hne, fun δ hδ => ?_⟩
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have h1 := isMVtx_iff_of_adj _ hδ
    have h2 := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  have h1 := burnsideMag568_commutator_zE_ltil_le h hb hU hbad hEf hET hcard hRG 1 hδM
    (by rwa [one_smul])
  have hz : mag568_zE h E 1 =
      Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) := by
    ext x
    simp [burnsideMag568_zE_def]
  rwa [hz] at h1

theorem burnsideMag568_centerOf_vb_smul (h : PUHyp M T L) (k : (puAmalgam h.le).Universal)
    (x : Vtx (puAmalgam h.le)) :
    centerOf (burnsideSL3G_vb (puAmalgam h.le) (k • x)) =
      (centerOf (burnsideSL3G_vb (puAmalgam h.le) x)).map (MulAut.conj k).toMonoidHom := by
  rw [burnsideSL3G_vb, burnsideSL3G_vb, vi_smul, PU.centerOf_map (MulAut.conj k).injective]

theorem burnsideMag568_good_all (h : PUHyp M T L) (hgood : ¬ mag568_Bad h)
    (y : Vtx (puAmalgam h.le)) (hy : IsMVtx _ y) :
    ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) y), Ltil h.le L y⁆ ≤ ZM _ y := by
  unfold mag568_Bad at hgood
  push Not at hgood
  obtain ⟨x, hx, hxg⟩ := hgood
  obtain ⟨k, rfl⟩ := exists_smul_eq_of_isMVtx _ hx hy
  have hL : Ltil h.le L (k • x) = (Ltil h.le L x).map (MulAut.conj k).toMonoidHom :=
    puTrans_smul h.le (S4A.L_normal h) k x
  rw [burnsideMag568_centerOf_vb_smul h k x, hL, ← Subgroup.map_commutator, zm_smul]
  exact Subgroup.map_mono hxg

theorem burnsideMag568_key_of_good (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hU : IsSL3U M T L) (hgood : ¬ mag568_Bad h) :
    ∃ E : Subgroup (puAmalgam h.le).Universal, E ≤ S34F.flat h (baseA _) ∧
      Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≠ ⊥ ∧
      ∀ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
        ⁅Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal),
          Ltil h.le L δ⁆ ≤ ZM _ δ := by
  have hall := burnsideMag568_good_all h hgood
  refine ⟨burnsideSL3G_wStar (puAmalgam h.le) (baseB _),
    burnsideSL3G_wStar_le_flat h hU (adj_baseA_baseB _).symm (PU.isMVtx_baseA _),
    burnsideSL3G_uloc_inf_centralizer_wStar_ne_bot h, fun δ hβδ => ?_⟩
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have h1 := isMVtx_iff_of_adj _ hβδ
    have h2 := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  exact (Subgroup.commutator_mono (burnsideSL3G_uloc_inf_centralizer_le_centerOf h hb
    (PU.isMVtx_baseA _) (adj_baseA_baseB _) hβδ hδM) le_rfl).trans (hall δ hδM)

theorem burnsideMag568_slGt4Key : SLGt4Key := by
  intro G _ _ M T L h _ hb hU _
  by_cases hbad : mag568_Bad h
  · exact burnsideMag568_key_of_bad h hb hU hbad
  · exact burnsideMag568_key_of_good h hb hU hbad

theorem burnsideMag568_noNonlinSLGt4 : NoNonlinSLGt4 :=
  noNonlinSLGt4_of_key burnsideMag568_slGt4Key

end CFSG.Quasithin.MS93.S4L
