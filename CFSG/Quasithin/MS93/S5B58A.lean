module

public import CFSG.Quasithin.MS93.S5B57

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5B

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section BSub

theorem vv_le_qv (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) : Vv (puAmalgam h.le) γ ≤ Qv _ γ := by
  refine iSup₂_le fun ρ hρ => ?_
  have hρ' : (puAmalgam h.le).treeGraph.dist γ ρ ≤ 2 := hρ
  by_cases hρM : IsMVtx _ ρ
  · rw [zv_of_isMVtx _ hρM]
    exact zm_le_qv_of_dist_lt _ hρM (by rw [SimpleGraph.dist_comm]; omega)
  · rw [zv_of_not_isMVtx _ hρM]
    have hd1 : (puAmalgam h.le).treeGraph.dist γ ρ = 1 := by
      have h0 : (puAmalgam h.le).treeGraph.dist γ ρ ≠ 0 := fun h0 => by
        rw [(dist_eq_zero_iff _).1 h0] at hγ
        exact hρM hγ
      have hodd : ¬ Even ((puAmalgam h.le).treeGraph.dist γ ρ) := fun he =>
        hρM (((even_dist_iff _ _ _).1 he).1 hγ)
      have h2 : (puAmalgam h.le).treeGraph.dist γ ρ ≠ 2 := fun h2 => hodd (h2 ▸ even_two)
      omega
    exact (zh_le_zm _ (SimpleGraph.dist_eq_one_iff_adj.1 hd1)).trans
      (zm_le_qv_self _ hγ h.critDist_pos)

theorem commutator_mem_zm_of_mem_bSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ S5.bSub h.le L γ) {l : (puAmalgam h.le).Universal} (hl : l ∈ puTrans h.le L γ) :
    ⁅x, l⁆ ∈ ZM _ γ := by
  have hst : ∀ g ∈ S5.bSub h.le L γ, g ∈ Subgroup.normalizer (ZM _ γ : Set _) := by
    intro g hg
    refine stab_le_normalizer_zm _ _ (qv_le_stab _ _ ?_)
    refine (Subgroup.closure_le _).2 ?_ hg
    rintro v ⟨hv, -⟩
    exact vv_le_qv h hb hγ hv
  have hx' : x ∈ Subgroup.closure {v | v ∈ Vv (puAmalgam h.le) γ ∧
      ∀ y ∈ puTrans h.le L γ, ⁅v, y⁆ ∈ ZM (puAmalgam h.le) γ} := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem v hv => exact hv.2 l hl
  | one => simp
  | mul a b ha _ iha ihb =>
    have e : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hst a ha) _).1 ihb) iha
  | inv a ha iha =>
    have e : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hst a ha)) _).1 (inv_mem iha)
    simpa using this

end BSub

section Trans

theorem exists_puTrans_mul (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    (hδ : (puAmalgam h.le).treeGraph.Adj (baseA _) δ) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) :
    ∃ l ∈ puTrans h.le L (baseA _), ∃ t ∈ Qv _ δ, g = l * t := by
  obtain ⟨g₀, hg₀, hg₀δ⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)) hδ
  have hQδ : Qv _ δ = (imM h.le T).map (MulAut.conj g₀).toMonoidHom := by
    rw [← hg₀δ, qv_smul, puAmalgam.qv_baseB]
  have hg' : g₀⁻¹ * g * g₀ ∈ stab _ (baseA (puAmalgam h.le)) :=
    mul_mem (mul_mem (inv_mem hg₀) hg) hg₀
  rw [puAmalgam.stab_baseA] at hg'
  obtain ⟨m, -, hm⟩ := hg'
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hsup : L.subgroupOf M ⊔ T.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.L_le h.le, ← h.eq_sup, Subgroup.subgroupOf_self]
  have hmem : m ∈ L.subgroupOf M ⊔ T.subgroupOf M := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨g₀ * (puAmalgam h.le).ofA l * g₀⁻¹, ?_, g₀ * (puAmalgam h.le).ofA t * g₀⁻¹, ?_, ?_⟩
  · have hlL : (puAmalgam h.le).ofA l ∈ puTrans h.le L (baseA _) := by
      rw [puTrans_L_baseA h]
      exact ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_puTrans h.le hLn _ hg₀) _).1 hlL
  · rw [hQδ]
    exact ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  · calc g = g₀ * (g₀⁻¹ * g * g₀) * g₀⁻¹ := by group
      _ = g₀ * ((puAmalgam h.le).ofA l * (puAmalgam h.le).ofA t) * g₀⁻¹ := by
        rw [← hm, ← hlt, map_mul]
      _ = _ := by group

theorem exists_puTrans_smul (h : PUHyp M T L) {γ ε ε' : Vtx (puAmalgam h.le)}
    (hγ : IsMVtx _ γ) (hγε : (puAmalgam h.le).treeGraph.Adj γ ε)
    (hγε' : (puAmalgam h.le).treeGraph.Adj γ ε') : ∃ l ∈ puTrans h.le L γ, l • ε = ε' := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hγ
  have h1 : (puAmalgam h.le).treeGraph.Adj (baseA _) (g⁻¹ • ε) := by
    have := (adj_smul _ g⁻¹ _ _).2 hγε
    rwa [inv_smul_smul] at this
  have h1' : (puAmalgam h.le).treeGraph.Adj (baseA _) (g⁻¹ • ε') := by
    have := (adj_smul _ g⁻¹ _ _).2 hγε'
    rwa [inv_smul_smul] at this
  obtain ⟨y, hy, hyε⟩ := exists_mem_stab_smul _ h1 h1'
  obtain ⟨l, hl, t, ht, rfl⟩ := exists_puTrans_mul h h1 hy
  refine ⟨g * l * g⁻¹, ?_, ?_⟩
  · rw [puTrans_smul h.le hLn]
    exact ⟨l, hl, rfl⟩
  · have ht' : t • (g⁻¹ • ε) = g⁻¹ • ε := (mem_stab _).1 (qv_le_stab _ _ ht)
    rw [mul_smul, ht'] at hyε
    rw [mul_smul, mul_smul, hyε, smul_inv_smul]

end Trans

section Path

theorem uSub_inf_bSub_le_qv (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {γ ε ε' ρ ν : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγε : (puAmalgam h.le).treeGraph.Adj γ ε) (hγε' : (puAmalgam h.le).treeGraph.Adj γ ε')
    (hερ : (puAmalgam h.le).treeGraph.Adj ε ρ)
    (hγν : (puAmalgam h.le).treeGraph.dist γ ν < critDist (puAmalgam h.le))
    (hε'ν : (puAmalgam h.le).treeGraph.dist ε' ν + 2 ≤ critDist (puAmalgam h.le)) :
    S5.uSub h.le L ρ ⊓ S5.bSub h.le L γ ≤ Qv _ ν := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨t, ht, htε⟩ := exists_puTrans_smul h hγ hγε hγε'
  have hρ : IsMVtx _ ρ := by
    have h1 := isMVtx_iff_of_adj _ hγε
    have h2 := isMVtx_iff_of_adj _ hερ
    tauto
  have htρ : IsMVtx _ (t • ρ) := (isMVtx_smul _ t ρ).2 hρ
  have hadj : (puAmalgam h.le).treeGraph.Adj ε' (t • ρ) := by
    rw [← htε]
    exact (adj_smul _ t _ _).2 hερ
  have hdist : (puAmalgam h.le).treeGraph.dist (t • ρ) ν < critDist (puAmalgam h.le) := by
    have h1 := dist_triangle _ (t • ρ) ε' ν
    have h2 : (puAmalgam h.le).treeGraph.dist (t • ρ) ε' = 1 := dist_eq_one_of_adj _ hadj.symm
    omega
  rintro u ⟨hu, huB⟩
  have hc : ⁅u, t⁆ ∈ ZM _ γ := commutator_mem_zm_of_mem_bSub h hb hγ huB ht
  have hut : t * u * t⁻¹ ∈ S5.uSub h.le L (t • ρ) := by
    rw [uSub_smul h.le hLn]
    exact ⟨u, hu, rfl⟩
  have e : u = ⁅u, t⁆ * (t * u * t⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (zm_le_qv_of_dist_lt _ hγ hγν hc)
    (zm_le_qv_of_dist_lt _ htρ hdist (uSub_le_zm h.le _ hut))

theorem relIndex_bSub_uSub_le (h : PUHyp M T L) {n : ℕ}
    (hP : ∀ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
      (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ n)
    {γ ε ρ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hγε : (puAmalgam h.le).treeGraph.Adj γ ε)
    (hερ : (puAmalgam h.le).treeGraph.Adj ε ρ) :
    (S5.bSub h.le L γ).relIndex (S5.uSub h.le L ρ) ≤ n := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hγ hγε
  have hρ : (puAmalgam h.le).treeGraph.Adj (baseB _) (g⁻¹ • ρ) := by
    have := (adj_smul _ g⁻¹ _ _).2 hερ
    rwa [inv_smul_smul] at this
  have e : (S5.bSub h.le L (g • baseA (puAmalgam h.le))).relIndex (S5.uSub h.le L ρ) =
      (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L (g⁻¹ • ρ)) := by
    conv_lhs => rw [← smul_inv_smul g ρ]
    rw [bSub_smul h.le hLn, uSub_smul h.le hLn,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  rw [e]
  exact hP _ hρ

theorem stab_le_normalizer_of_uSub_le_bSub (h : PUHyp M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hU : S5.uSub h.le L δ ≤ S5.bSub h.le L (baseA _)) :
    stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer ((ZM _ δ ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hδ : IsMVtx _ δ := by
    have := isMVtx_iff_of_adj _ hβδ
    have hβ := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  have hZX : ZM _ δ ⊔ XM _ (baseA (puAmalgam h.le)) =
      S5.uSub h.le L δ ⊔ XM _ (baseA (puAmalgam h.le)) := by
    rw [zm_eq_zh_sup_uSub h hδ hβδ.symm]
    have hZβ : ZH _ (baseB (puAmalgam h.le)) ≤ XM _ (baseA (puAmalgam h.le)) :=
      (zh_le_zm _ hαβ).trans (zm_le_xm _ hyp hb0 hα)
    exact le_antisymm (sup_le (sup_le (hZβ.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  intro g hg
  obtain ⟨l, hl, t, ht, rfl⟩ := exists_puTrans_mul h hαβ hg
  refine mul_mem ?_ ?_
  · rw [hZX]
    refine le_normalizer_sup_of_commutator_le
      ((puTrans_le_stab h.le L _).trans (stab_le_normalizer_xm _ _)) ?_ hl
    rw [Subgroup.commutator_le]
    intro u hu l' hl'
    exact Subgroup.mem_sup_right ((zm_le_xm _ hyp hb0 hα)
      (commutator_mem_zm_of_mem_bSub h hb hα (hU hu) hl'))
  · exact le_normalizer_sup ((qv_le_stab_of_adj _ hβδ).trans (stab_le_normalizer_zm _ _))
      ((qv_le_stab_of_isMVtx _ hyp hα hαβ).trans (stab_le_normalizer_xm _ _)) ht

theorem exists_uSub_not_le_bSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le)) :
    ∃ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ ∧
      ¬ S5.uSub h.le L δ ≤ S5.bSub h.le L (baseA _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hb2 := two_le_critDist _ hyp hb0
  obtain ⟨α', hc, -⟩ := exists_isCritical_geo _ hyp hb0 (isMVtx_baseA (puAmalgam h.le))
    (adj_baseA_baseB (puAmalgam h.le))
  have hcr := ms22_iii _ hyp hb0 hC hc
  have hd : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) := hcr.2.1
  set a₁ := geo _ α' (baseA (puAmalgam h.le)) 1
  set a₂ := geo _ α' (baseA (puAmalgam h.le)) 2
  have ha₂ : IsMVtx _ a₂ := isMVtx_geo_two _ hyp hb0 hcr
  have ha₂₁ : (puAmalgam h.le).treeGraph.Adj a₂ a₁ := (adj_geo _ (i := 1) (by omega)).symm
  have ha₁ : (puAmalgam h.le).treeGraph.Adj a₁ α' := (adj_geo_one _ (by omega)).symm
  obtain ⟨g, hg₂, hg₁⟩ := exists_smul_base_edge _ ha₂ ha₂₁
  have hc' : IsCritical _ (g⁻¹ • α') (g⁻¹ • baseA (puAmalgam h.le)) :=
    (isCritical_smul _ g⁻¹ _ _).2 hcr
  have hgeo : geo _ (g⁻¹ • α') (g⁻¹ • baseA (puAmalgam h.le)) 2 = baseA _ := by
    rw [geo_smul]
    change g⁻¹ • a₂ = _
    rw [hg₂, inv_smul_smul]
  have hiv := ms22_iv _ hyp hb0 hC hc'
  rw [hgeo] at hiv
  refine ⟨g⁻¹ • α', ?_, fun hU => hiv (stab_le_normalizer_of_uSub_le_bSub h hb ?_ hU)⟩ <;>
  · have := (adj_smul _ g⁻¹ _ _).2 ha₁
    rwa [hg₁, inv_smul_smul] at this

end Path

end S5B

end CFSG.Quasithin.MS93
