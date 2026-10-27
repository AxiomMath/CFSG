module

public import CFSG.Quasithin.MS93.Sec2Geo
public import CFSG.Quasithin.MS93.Sec2Gen

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem dist_le_one_iff {δ ρ : Vtx X} : X.treeGraph.dist δ ρ ≤ 1 ↔ ρ = δ ∨ X.treeGraph.Adj δ ρ := by
  constructor
  · intro h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
    · exact Or.inl ((dist_eq_zero_iff X).mp h0).symm
    · exact Or.inr (dist_eq_one_iff_adj.mp h1)
  · rintro (rfl | h)
    · simp
    · rw [dist_eq_one_of_adj X h]

theorem mem_stab {x : X.Universal} {δ : Vtx X} : x ∈ stab X δ ↔ x • δ = δ :=
  MulAction.mem_stabilizer_iff

theorem mem_kerAt {x : X.Universal} {δ : Vtx X} {i : ℕ} :
    x ∈ kerAt X δ i ↔ ∀ ρ, X.treeGraph.dist δ ρ ≤ i → x ∈ stab X ρ := by
  simp [kerAt, Subgroup.mem_iInf]

theorem mem_qv {x : X.Universal} {δ : Vtx X} :
    x ∈ Qv X δ ↔ x ∈ stab X δ ∧ ∀ ρ, X.treeGraph.Adj δ ρ → x ∈ stab X ρ := by
  rw [Qv, mem_kerAt]
  constructor
  · intro h
    exact ⟨h δ (by simp), fun ρ hρ => h ρ (by rw [dist_eq_one_of_adj X hρ])⟩
  · rintro ⟨h1, h2⟩ ρ hρ
    rcases (dist_le_one_iff X).mp hρ with rfl | hρ
    · exact h1
    · exact h2 ρ hρ

theorem kerAt_le_stab (δ : Vtx X) (i : ℕ) : kerAt X δ i ≤ stab X δ := fun _ hx =>
  (mem_kerAt X).mp hx δ (by simp)

theorem qv_le_stab (δ : Vtx X) : Qv X δ ≤ stab X δ := kerAt_le_stab X δ 1

theorem qv_le_stab_of_adj {δ ρ : Vtx X} (h : X.treeGraph.Adj δ ρ) : Qv X δ ≤ stab X ρ :=
  fun _ hx => ((mem_qv X).mp hx).2 ρ h

theorem stab_smul (g : X.Universal) (δ : Vtx X) :
    stab X (g • δ) = (stab X δ).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g δ

theorem mem_stab_smul {x g : X.Universal} {δ : Vtx X} :
    x ∈ stab X (g • δ) ↔ g⁻¹ * x * g ∈ stab X δ := by
  rw [stab_smul, mem_map_conj]

theorem kerAt_smul (g : X.Universal) (δ : Vtx X) (i : ℕ) :
    kerAt X (g • δ) i = (kerAt X δ i).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_conj, mem_kerAt, mem_kerAt]
  constructor
  · intro h ρ hρ
    have := h (g • ρ) (by rwa [dist_smul])
    rwa [mem_stab_smul] at this
  · intro h ρ hρ
    have hρ' : X.treeGraph.dist δ (g⁻¹ • ρ) ≤ i := by
      rw [← dist_smul X g, smul_inv_smul]
      exact hρ
    have := h _ hρ'
    rw [← mem_stab_smul, smul_inv_smul] at this
    exact this

theorem qv_smul (g : X.Universal) (δ : Vtx X) :
    Qv X (g • δ) = (Qv X δ).map (MulAut.conj g).toMonoidHom := kerAt_smul X g δ 1

theorem zh_smul (g : X.Universal) (δ : Vtx X) :
    ZH X (g • δ) = (ZH X δ).map (MulAut.conj g).toMonoidHom := by
  rw [ZH, ZH, qv_smul, omegaOneCenterOf_map_mulEquiv]

theorem xm_smul (g : X.Universal) (δ : Vtx X) :
    XM X (g • δ) = (XM X δ).map (MulAut.conj g).toMonoidHom := by
  rw [XM, XM, qv_smul, omegaOneCenterOf_map_mulEquiv]

private theorem iSup_smul {S : Vtx X → Set (Vtx X)}
    (hS : ∀ (g : X.Universal) δ ρ, g • ρ ∈ S (g • δ) ↔ ρ ∈ S δ)
    {F : Vtx X → Subgroup X.Universal}
    (hF : ∀ (g : X.Universal) ρ, F (g • ρ) = (F ρ).map (MulAut.conj g).toMonoidHom)
    (g : X.Universal) (δ : Vtx X) :
    (⨆ ρ ∈ S (g • δ), F ρ) = (⨆ ρ ∈ S δ, F ρ).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun ρ hρ => ?_
    have hρ' : g⁻¹ • ρ ∈ S δ := by
      rw [← hS g, smul_inv_smul]
      exact hρ
    calc F ρ = F (g • (g⁻¹ • ρ)) := by rw [smul_inv_smul]
      _ = (F (g⁻¹ • ρ)).map (MulAut.conj g).toMonoidHom := hF g _
      _ ≤ _ := Subgroup.map_mono (le_iSup₂_of_le (g⁻¹ • ρ) hρ' le_rfl)
  · rw [Subgroup.map_iSup]
    refine iSup_le fun ρ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hρ => ?_
    rw [← hF]
    exact le_iSup₂_of_le (g • ρ) ((hS g δ ρ).mpr hρ) le_rfl

theorem zm_smul (g : X.Universal) (δ : Vtx X) :
    ZM X (g • δ) = (ZM X δ).map (MulAut.conj g).toMonoidHom :=
  iSup_smul X (S := X.treeGraph.neighborSet)
    (fun g δ ρ => by simp only [mem_neighborSet, adj_smul]) (zh_smul X) g δ

theorem zv_smul (g : X.Universal) (δ : Vtx X) :
    Zv X (g • δ) = (Zv X δ).map (MulAut.conj g).toMonoidHom := by
  by_cases h : IsMVtx X δ
  · rw [zv_of_isMVtx X h, zv_of_isMVtx X ((isMVtx_smul X g δ).mpr h), zm_smul]
  · rw [zv_of_not_isMVtx X h, zv_of_not_isMVtx X (by rwa [isMVtx_smul]), zh_smul]

theorem vi_smul (g : X.Universal) (δ : Vtx X) (i : ℕ) :
    Vi X (g • δ) i = (Vi X δ i).map (MulAut.conj g).toMonoidHom :=
  iSup_smul X (S := fun δ => {ρ | X.treeGraph.dist δ ρ ≤ i})
    (fun g δ ρ => by simp only [Set.mem_ofPred_eq, dist_smul]) (zv_smul X) g δ

theorem cm_smul (g : X.Universal) (δ : Vtx X) :
    CM X (g • δ) = (CM X δ).map (MulAut.conj g).toMonoidHom := by
  rw [CM, CM, stab_smul, zm_smul, ← centralizer_map_mulEquiv,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

theorem isCritical_smul (g : X.Universal) (α α' : Vtx X) :
    IsCritical X (g • α) (g • α') ↔ IsCritical X α α' := by
  rw [IsCritical, IsCritical, isMVtx_smul, dist_smul, zm_smul, qv_smul,
    map_conj_le_map_conj_iff]

theorem stab_le_normalizer_of_smul {F : Vtx X → Subgroup X.Universal}
    (hF : ∀ (g : X.Universal) ρ, F (g • ρ) = (F ρ).map (MulAut.conj g).toMonoidHom) (δ : Vtx X) :
    stab X δ ≤ Subgroup.normalizer (F δ : Set X.Universal) :=
  le_normalizer_of_map_conj_le fun h hh => by rw [← hF, (mem_stab X).mp hh]

theorem stab_le_normalizer_qv (δ : Vtx X) :
    stab X δ ≤ Subgroup.normalizer (Qv X δ : Set X.Universal) :=
  stab_le_normalizer_of_smul X (qv_smul X) δ

theorem stab_le_normalizer_zh (δ : Vtx X) :
    stab X δ ≤ Subgroup.normalizer (ZH X δ : Set X.Universal) :=
  stab_le_normalizer_of_smul X (zh_smul X) δ

theorem stab_le_normalizer_zm (δ : Vtx X) :
    stab X δ ≤ Subgroup.normalizer (ZM X δ : Set X.Universal) :=
  stab_le_normalizer_of_smul X (zm_smul X) δ

theorem stab_le_normalizer_xm (δ : Vtx X) :
    stab X δ ≤ Subgroup.normalizer (XM X δ : Set X.Universal) :=
  stab_le_normalizer_of_smul X (xm_smul X) δ

theorem exists_eq_smul_baseA {α : Vtx X} (hα : IsMVtx X α) :
    ∃ g : X.Universal, α = g • baseA X := by
  rcases exists_smul_base X α with h | ⟨g, rfl⟩
  · exact h
  · exact absurd ((isMVtx_smul X g _).mp hα) (not_isMVtx_baseB X)

theorem exists_eq_smul_baseB {β : Vtx X} (hβ : ¬ IsMVtx X β) :
    ∃ g : X.Universal, β = g • baseB X := by
  rcases exists_smul_base X β with ⟨g, rfl⟩ | h
  · exact absurd ((isMVtx_smul X g _).mpr (isMVtx_baseA X)) hβ
  · exact h

theorem exists_smul_base_edge {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β) :
    ∃ g : X.Universal, α = g • baseA X ∧ β = g • baseB X := by
  obtain ⟨g, h | h⟩ := exists_smul_edge X hαβ
  · exact ⟨g, h⟩
  · exact absurd (h.1 ▸ hα) (by rw [isMVtx_smul]; exact not_isMVtx_baseB X)

theorem exists_smul_edge_of_isMVtx {α β α' β' : Vtx X} (hα : IsMVtx X α)
    (hαβ : X.treeGraph.Adj α β) (hα' : IsMVtx X α') (hαβ' : X.treeGraph.Adj α' β') :
    ∃ g : X.Universal, g • α = α' ∧ g • β = β' := by
  obtain ⟨g₁, rfl, rfl⟩ := exists_smul_base_edge X hα hαβ
  obtain ⟨g₂, rfl, rfl⟩ := exists_smul_base_edge X hα' hαβ'
  exact ⟨g₂ * g₁⁻¹, by rw [smul_smul, inv_mul_cancel_right],
    by rw [smul_smul, inv_mul_cancel_right]⟩

theorem exists_smul_eq_of_isMVtx {α α' : Vtx X} (hα : IsMVtx X α) (hα' : IsMVtx X α') :
    ∃ g : X.Universal, g • α = α' := by
  obtain ⟨g₁, rfl⟩ := exists_eq_smul_baseA X hα
  obtain ⟨g₂, rfl⟩ := exists_eq_smul_baseA X hα'
  exact ⟨g₂ * g₁⁻¹, by rw [smul_smul, inv_mul_cancel_right]⟩

theorem exists_mem_stab_smul {δ ρ ρ' : Vtx X} (h : X.treeGraph.Adj δ ρ)
    (h' : X.treeGraph.Adj δ ρ') : ∃ g ∈ stab X δ, g • ρ = ρ' := by
  by_cases hδ : IsMVtx X δ
  · obtain ⟨g, hg, hg'⟩ := exists_smul_edge_of_isMVtx X hδ h hδ h'
    exact ⟨g, (mem_stab X).mpr hg, hg'⟩
  · have hρ : IsMVtx X ρ := by
      have := (isMVtx_iff_of_adj X h.symm)
      tauto
    have hρ' : IsMVtx X ρ' := by
      have := (isMVtx_iff_of_adj X h'.symm)
      tauto
    obtain ⟨g, hg, hg'⟩ := exists_smul_edge_of_isMVtx X hρ h.symm hρ' h'.symm
    exact ⟨g, (mem_stab X).mpr hg', hg⟩

theorem exists_adj (δ : Vtx X) : ∃ ρ, X.treeGraph.Adj δ ρ := by
  rcases exists_smul_base X δ with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨g • baseB X, (adj_smul X g _ _).mpr (adj_baseA_baseB X)⟩
  · exact ⟨g • baseA X, (adj_smul X g _ _).mpr (adj_baseA_baseB X).symm⟩

abbrev edgeImage : Subgroup X.Universal := (Monoid.PushoutI.base X.diagram).range

theorem edgeImage_eq_inf : edgeImage X = X.ofA.range ⊓ X.ofB.range :=
  X.ofA_range_inf_ofB_range.symm

theorem qv_baseB (h : Hyp20 X) : Qv X (baseB X) = edgeImage X := by
  apply le_antisymm
  · intro x hx
    rw [edgeImage_eq_inf]
    refine ⟨?_, ?_⟩
    · rw [← stabilizer_baseA]
      exact qv_le_stab_of_adj X (adj_baseA_baseB X).symm hx
    · rw [← stabilizer_baseB]
      exact qv_le_stab X _ hx
  · rintro _ ⟨c, rfl⟩
    rw [mem_qv]
    refine ⟨?_, fun ρ hρ => ?_⟩
    · show _ ∈ MulAction.stabilizer X.Universal (baseB X)
      rw [stabilizer_baseB, ← X.ofB_toB]
      exact ⟨_, rfl⟩
    · obtain ⟨b, rfl⟩ := (adj_baseB_iff X ρ).mp hρ
      have hρ' : (Sum.inl ((X.ofB b : X.Universal) : X.Universal ⧸ X.ofA.range) : Vtx X) =
          X.ofB b • baseA X := (smul_baseA X _).symm
      rw [hρ', mem_stab_smul]
      show _ ∈ MulAction.stabilizer X.Universal (baseA X)
      rw [stabilizer_baseA]
      obtain ⟨c', hc'⟩ : b⁻¹ * X.toB c * b ∈ X.edgeB := by
        have := h.normal_edgeB.conj_mem _ (X.toA_mem_edgeA c |> fun _ => ⟨c, rfl⟩) b⁻¹
        simpa using this
      refine ⟨X.toA c', ?_⟩
      rw [X.ofA_toA, ← X.ofB_toB, hc', map_mul, map_mul, map_inv, ← X.ofB_toB]

theorem qv_smul_baseB (h : Hyp20 X) (g : X.Universal) :
    Qv X (g • baseB X) = (edgeImage X).map (MulAut.conj g).toMonoidHom := by
  rw [qv_smul, qv_baseB X h]

theorem qv_eq_stab_inf (h : Hyp20 X) {α β : Vtx X} (hα : IsMVtx X α)
    (hαβ : X.treeGraph.Adj α β) : Qv X β = stab X β ⊓ stab X α := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge X hα hαβ
  rw [qv_smul_baseB X h, stab_smul, stab_smul, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    stab, stab, stabilizer_baseA, stabilizer_baseB, inf_comm, edgeImage_eq_inf]

theorem qv_le_qv (h : Hyp20 X) {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β) :
    Qv X α ≤ Qv X β := by
  rw [qv_eq_stab_inf X h hα hαβ]
  exact le_inf (qv_le_stab_of_adj X hαβ) (qv_le_stab X α)

theorem qv_le_stab_of_isMVtx (h : Hyp20 X) {α β : Vtx X} (hα : IsMVtx X α)
    (hαβ : X.treeGraph.Adj α β) : Qv X β ≤ stab X α := by
  rw [qv_eq_stab_inf X h hα hαβ]
  exact inf_le_right

theorem qv_le_stab_of_dist_le_two (h : Hyp20 X) {α ρ : Vtx X} (hα : IsMVtx X α)
    (hρ : X.treeGraph.dist α ρ ≤ 2) : Qv X α ≤ stab X ρ := by
  rcases Nat.lt_or_ge (X.treeGraph.dist α ρ) 2 with h2 | h2
  · rcases (dist_le_one_iff X (δ := α) (ρ := ρ)).mp (by omega) with rfl | hαρ
    · exact qv_le_stab X _
    · exact qv_le_stab_of_adj X hαρ
  · have hd : X.treeGraph.dist α ρ = 2 := le_antisymm hρ h2
    have hadj := adj_geo X (show 1 < X.treeGraph.dist α ρ by omega)
    have h1 : X.treeGraph.Adj α (geo X α ρ 1) := adj_geo_one X (by omega)
    rw [show (1 + 1 : ℕ) = 2 from rfl, ← hd, geo_dist] at hadj
    exact (qv_le_qv X h hα h1).trans (qv_le_stab_of_adj X hadj)

theorem le_qv_of_normalizer (h : Hyp20 X) {α β : Vtx X} (hα : IsMVtx X α)
    (hαβ : X.treeGraph.Adj α β) {N : Subgroup X.Universal} (hN : N ≤ Qv X β)
    (hNα : stab X α ≤ Subgroup.normalizer (N : Set X.Universal)) : N ≤ Qv X α := by
  intro x hx
  rw [mem_qv]
  refine ⟨qv_le_stab_of_isMVtx X h hα hαβ (hN hx), fun ρ hρ => ?_⟩
  obtain ⟨g, hg, rfl⟩ := exists_mem_stab_smul X hαβ hρ
  rw [mem_stab_smul]
  have hx' : g⁻¹ * x * g ∈ N := by
    rw [← map_conj_eq_of_mem_normalizer (hNα hg), mem_map_conj] at hx
    exact hx
  exact qv_le_stab X β (hN hx')

theorem edge_universalCompletion : X.universalCompletion.edge = edgeImage X := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (X.ofA_toA c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, X.ofA_toA c⟩

theorem eq_bot_of_normal_le_edgeImage (h : Hyp20 X) {K : Subgroup X.Universal} (hK : K.Normal)
    (hKle : K ≤ edgeImage X) : K = ⊥ :=
  (X.universalCompletion.isFaithful_iff).mp h.faithful K hK
    (by rw [edge_universalCompletion]; exact hKle)

theorem stab_sup_stab (g : X.Universal) :
    stab X (g • baseA X) ⊔ stab X (g • baseB X) = ⊤ := by
  rw [stab_smul, stab_smul, ← Subgroup.map_sup, stab, stab, stabilizer_baseA, stabilizer_baseB,
    X.ofA_range_sup_ofB_range, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective

theorem ms21_iii (h : Hyp20 X) {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β)
    {K : Subgroup X.Universal} (hK : K ≤ Qv X β)
    (hKα : stab X α ≤ Subgroup.normalizer (K : Set X.Universal))
    (hKβ : stab X β ≤ Subgroup.normalizer (K : Set X.Universal)) : K = ⊥ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge X hα hαβ
  have hnorm : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← stab_sup_stab X g]
    exact sup_le hKα hKβ
  refine eq_bot_of_normal_le_edgeImage X h hnorm ?_
  rw [qv_smul_baseB X h] at hK
  intro x hx
  have := hK (hnorm.conj_mem x hx g)
  rw [mem_map_conj] at this
  simpa [mul_assoc] using this

theorem qv_eq_range (h : Hyp20 X) (g : X.Universal) :
    Qv X (g • baseB X) =
      ((MulAut.conj g).toMonoidHom.comp (Monoid.PushoutI.base X.diagram)).range := by
  rw [qv_smul_baseB X h, MonoidHom.range_comp]

theorem base_injective : Function.Injective (Monoid.PushoutI.base X.diagram) :=
  Monoid.PushoutI.base_injective X.diagram_injective

theorem exists_mulEquiv_qv (h : Hyp20 X) {β : Vtx X} (hβ : ¬ IsMVtx X β) :
    Nonempty (C ≃* Qv X β) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseB X hβ
  rw [qv_eq_range X h g]
  exact ⟨MonoidHom.ofInjective ((MulAut.conj g).injective.comp (base_injective X))⟩

theorem finite_qv (h : Hyp20 X) {β : Vtx X} (hβ : ¬ IsMVtx X β) : Finite (Qv X β) := by
  obtain ⟨e⟩ := exists_mulEquiv_qv X h hβ
  have := h.finite_edge
  exact Finite.of_equiv _ e.toEquiv

theorem isPGroup_qv (h : Hyp20 X) {β : Vtx X} (hβ : ¬ IsMVtx X β) : IsPGroup 2 (Qv X β) := by
  obtain ⟨e⟩ := exists_mulEquiv_qv X h hβ
  exact h.isPGroup_edge.of_equiv e

theorem nontrivial_qv (h : Hyp20 X) {β : Vtx X} (hβ : ¬ IsMVtx X β) : Nontrivial (Qv X β) := by
  obtain ⟨e⟩ := exists_mulEquiv_qv X h hβ
  have := h.nontrivial_edge
  exact e.toEquiv.symm.nontrivial

theorem qv_ne_bot (h : Hyp20 X) {β : Vtx X} (hβ : ¬ IsMVtx X β) : Qv X β ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot _).mp (nontrivial_qv X h hβ)

theorem isNilpotent_qv (h : Hyp20 X) {β : Vtx X} (hβ : ¬ IsMVtx X β) :
    Group.IsNilpotent (Qv X β) := by
  have := finite_qv X h hβ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isPGroup_qv X h hβ).isNilpotent

theorem omegaOneCenterOf_ne_bot {G : Type*} [Group G] {P : Subgroup G} [Finite P]
    (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) : omegaOneCenterOf P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨n, hn, hcard⟩ := hP.nontrivial_iff_card.mp inferInstance
  have h2 : 2 ∣ Nat.card P := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  have h2z : 2 ∣ Nat.card (Subgroup.center P) := Group.IsNilpotent.prime_dvd_card_center h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2z
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hmem : ((z : P) : G) ∈ omegaOneCenterOf P := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨(z : P).2, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
    · have := congrArg (fun w : Subgroup.center P => ((w : P) : G)) hz2
      simpa using this
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  omega

theorem zh_ne_bot (h : Hyp20 X) {β : Vtx X} (hβ : ¬ IsMVtx X β) : ZH X β ≠ ⊥ := by
  have := finite_qv X h hβ
  exact omegaOneCenterOf_ne_bot (isPGroup_qv X h hβ) (qv_ne_bot X h hβ)

theorem not_stab_le_normalizer_qv (h : Hyp20 X) {α β : Vtx X} (hα : IsMVtx X α)
    (hαβ : X.treeGraph.Adj α β) :
    ¬ stab X α ≤ Subgroup.normalizer (Qv X β : Set X.Universal) := fun hn =>
  qv_ne_bot X h ((isMVtx_iff_of_adj X hαβ).mp hα)
    (ms21_iii X h hα hαβ le_rfl hn (stab_le_normalizer_qv X β))

theorem zh_le_zm {α β : Vtx X} (hαβ : X.treeGraph.Adj α β) : ZH X β ≤ ZM X α :=
  le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ X.treeGraph.neighborSet α) => ZH X ρ) β hαβ le_rfl

theorem zh_le_qv (δ : Vtx X) : ZH X δ ≤ Qv X δ :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.1

theorem zh_le_centralizer (δ : Vtx X) :
    ZH X δ ≤ Subgroup.centralizer (Qv X δ : Set X.Universal) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.2

theorem xm_le_qv (δ : Vtx X) : XM X δ ≤ Qv X δ :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.1

theorem xm_le_centralizer (δ : Vtx X) :
    XM X δ ≤ Subgroup.centralizer (Qv X δ : Set X.Universal) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.2

theorem qv_le_centralizer_xm (δ : Vtx X) :
    Qv X δ ≤ Subgroup.centralizer (XM X δ : Set X.Universal) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact xm_le_centralizer X δ

theorem isElemAbelian_xm (δ : Vtx X) : CFSG.Open.IsElemAbelian 2 (XM X δ) := by
  refine ⟨(isMulCommutative_subgroup_iff).mpr fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact Subgroup.mem_centralizer_iff.mp (xm_le_centralizer X δ hy) x (xm_le_qv X δ hx)
  · induction hx using Subgroup.closure_induction with
    | mem x hx => exact hx.2
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x :=
        Subgroup.mem_centralizer_iff.mp (xm_le_centralizer X δ hy) x (xm_le_qv X δ hx)
      rw [(Commute.mul_pow hxy 2), ihx, ihy, one_mul]
    | inv x _ ih => rw [inv_pow, ih, inv_one]

theorem zm_le_centralizer_qv (h : Hyp20 X) {α : Vtx X} (hα : IsMVtx X α) :
    ZM X α ≤ Subgroup.centralizer (Qv X α : Set X.Universal) := by
  refine iSup₂_le fun ρ hρ => (zh_le_centralizer X ρ).trans ?_
  exact Subgroup.centralizer_le (qv_le_qv X h hα hρ)

theorem commutator_zm_qv (h : Hyp20 X) {α : Vtx X} (hα : IsMVtx X α) :
    ⁅ZM X α, Qv X α⁆ = ⊥ :=
  (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (zm_le_centralizer_qv X h hα)

theorem zm_le_qv_of_dist_lt {α γ : Vtx X} (hα : IsMVtx X α)
    (hd : X.treeGraph.dist α γ < critDist X) : ZM X α ≤ Qv X γ := by
  by_contra hle
  have hmem : X.treeGraph.dist α γ ∈ {n | ∃ α α' : Vtx X, IsMVtx X α ∧
      X.treeGraph.dist α α' = n ∧ ¬ ZM X α ≤ Qv X α'} := ⟨α, γ, hα, rfl, hle⟩
  exact absurd (Nat.sInf_le hmem) (not_le.mpr hd)

theorem zm_le_qv_self {α : Vtx X} (hα : IsMVtx X α) (hb : 0 < critDist X) : ZM X α ≤ Qv X α :=
  zm_le_qv_of_dist_lt X hα (by simpa using hb)

theorem zm_le_xm (h : Hyp20 X) (hb : 0 < critDist X) {α : Vtx X} (hα : IsMVtx X α) :
    ZM X α ≤ XM X α := by
  refine iSup₂_le fun ρ hρ => ?_
  show omegaOneOf (centerOf (Qv X ρ)) ≤ omegaOneOf (centerOf (Qv X α))
  apply Subgroup.closure_mono
  rintro x ⟨⟨hx1, hx2⟩, hx3⟩
  have hxZ : x ∈ ZM X α := zh_le_zm X hρ (Subgroup.subset_closure ⟨⟨hx1, hx2⟩, hx3⟩)
  exact ⟨⟨zm_le_qv_self X hα hb hxZ, Subgroup.centralizer_le (qv_le_qv X h hα hρ) hx2⟩, hx3⟩

theorem ms21_iv (h : Hyp20 X) {α : Vtx X} (hα : IsMVtx X α) :
    ⁅ZM X α, Qv X α⁆ = ⊥ ∧ (0 < critDist X → ZM X α ≤ XM X α) :=
  ⟨commutator_zm_qv X h hα, fun hb => zm_le_xm X h hb hα⟩

theorem isElemAbelian_zm (h : Hyp20 X) (hb : 0 < critDist X) {α : Vtx X} (hα : IsMVtx X α) :
    CFSG.Open.IsElemAbelian 2 (ZM X α) :=
  isElemAbelian_of_le (isElemAbelian_xm X α) (zm_le_xm X h hb hα)

theorem zm_le_qv_of_not_isMVtx (h : Hyp20 X) {α ρ : Vtx X} (hα : IsMVtx X α)
    (hρ : ¬ IsMVtx X ρ) (hd : X.treeGraph.dist α ρ ≤ critDist X) : ZM X α ≤ Qv X ρ := by
  have hpos : 0 < X.treeGraph.dist α ρ := by
    rcases Nat.eq_zero_or_pos (X.treeGraph.dist α ρ) with h0 | h0
    · rw [(dist_eq_zero_iff X).mp h0] at hα
      exact absurd hα hρ
    · exact h0
  set γ := geo X ρ α 1
  have hγ : X.treeGraph.Adj ρ γ := adj_geo_one X (by rw [dist_comm]; exact hpos)
  have hγd : X.treeGraph.dist α γ = X.treeGraph.dist α ρ - 1 := by
    rw [dist_comm, dist_geo_right X (by rw [dist_comm]; omega), dist_comm]
  have hγM : IsMVtx X γ := by
    have := isMVtx_iff_of_adj X hγ
    tauto
  exact (zm_le_qv_of_dist_lt X hα (by omega)).trans (qv_le_qv X h hγM hγ.symm)

theorem ms21_v (h : Hyp20 X) : Even (critDist X) := by
  by_cases hne : {n | ∃ α α' : Vtx X, IsMVtx X α ∧ X.treeGraph.dist α α' = n ∧
      ¬ ZM X α ≤ Qv X α'}.Nonempty
  · obtain ⟨α, α', hα, hd, hle⟩ := Nat.sInf_mem hne
    rw [← critDist] at hd
    rw [← hd, even_dist_iff]
    refine ⟨fun _ => ?_, fun _ => hα⟩
    by_contra hα'
    exact hle (zm_le_qv_of_not_isMVtx X h hα hα' hd.le)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [critDist, hne, Nat.sInf_empty]
    exact ⟨0, rfl⟩

theorem IsCritical.isMVtx_right (h : Hyp20 X) {α α' : Vtx X} (hc : IsCritical X α α') :
    IsMVtx X α' := by
  have := (even_dist_iff X α α').mp (hc.2.1 ▸ ms21_v X h)
  exact this.mp hc.1

theorem eq_bot_of_le_stab (h : Hyp20 X) {K : Subgroup X.Universal}
    (hK : ∀ δ, K ≤ stab X δ) : K = ⊥ := by
  set N : Subgroup X.Universal := ⨅ δ, stab X δ
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_iInf] at hn ⊢
    intro δ
    have h1 := hn (g⁻¹ • δ)
    rw [mem_stab_smul, inv_inv] at h1
    exact h1⟩
  have hle : N ≤ edgeImage X := by
    rw [edgeImage_eq_inf]
    refine le_inf ?_ ?_
    · rw [← stabilizer_baseA]
      exact iInf_le _ (baseA X)
    · rw [← stabilizer_baseB]
      exact iInf_le _ (baseB X)
  have := eq_bot_of_normal_le_edgeImage X h hN hle
  exact le_bot_iff.mp (this ▸ le_iInf hK)

theorem exists_isCritical (h : Hyp20 X) : ∃ α α' : Vtx X, IsCritical X α α' := by
  by_cases hne : {n | ∃ α α' : Vtx X, IsMVtx X α ∧ X.treeGraph.dist α α' = n ∧
      ¬ ZM X α ≤ Qv X α'}.Nonempty
  · obtain ⟨α, α', hα, hd, hle⟩ := Nat.sInf_mem hne
    exact ⟨α, α', hα, hd, hle⟩
  · exfalso
    have hall : ∀ α α' : Vtx X, IsMVtx X α → ZM X α ≤ Qv X α' := by
      intro α α' hα
      by_contra hle
      exact hne ⟨_, α, α', hα, rfl, hle⟩
    have hZ : ZM X (baseA X) = ⊥ := eq_bot_of_le_stab X h fun δ => by
      obtain ⟨ρ, hρ⟩ := exists_adj X δ
      exact (hall _ ρ (isMVtx_baseA X)).trans (qv_le_stab_of_adj X hρ.symm)
    exact zh_ne_bot X h (not_isMVtx_baseB X)
      (le_bot_iff.mp (hZ ▸ zh_le_zm X (adj_baseA_baseB X)))

theorem exists_isCritical_of_isMVtx (h : Hyp20 X) {α : Vtx X} (hα : IsMVtx X α) :
    ∃ α' : Vtx X, IsCritical X α α' := by
  obtain ⟨γ, γ', hc⟩ := exists_isCritical X h
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx X hc.1 hα
  exact ⟨g • γ', (isCritical_smul X g γ γ').mpr hc⟩

theorem exists_isCritical_geo (h : Hyp20 X) (hb : 0 < critDist X) {α β : Vtx X}
    (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β) :
    ∃ α' : Vtx X, IsCritical X α α' ∧ geo X α α' 1 = β := by
  obtain ⟨γ, hc⟩ := exists_isCritical_of_isMVtx X h hα
  have hd : 0 < X.treeGraph.dist α γ := hc.2.1 ▸ hb
  obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul X (adj_geo_one X hd) hαβ
  refine ⟨g • γ, ?_, ?_⟩
  · have := (isCritical_smul X g α γ).mpr hc
    rwa [(mem_stab X).mp hg] at this
  · have hgα : g • α = α := (mem_stab X).mp hg
    calc geo X α (g • γ) 1 = geo X (g • α) (g • γ) 1 := by rw [hgα]
      _ = g • geo X α γ 1 := geo_smul X g α γ 1
      _ = β := hgβ

end CFSG.Quasithin.MS93
