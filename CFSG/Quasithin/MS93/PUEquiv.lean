module

public import CFSG.Quasithin.MS93.Amalgam

public section

namespace CFSG.Quasithin.MS93.PU

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ

section Transport

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

theorem centerOf_map {f : G₁ →* G₂} (hf : Function.Injective f) (K : Subgroup G₁) :
    centerOf (K.map f) = (centerOf K).map f := by
  ext x
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hc⟩
    refine ⟨k, ⟨hk, fun w hw => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hc (f w) ⟨w, hw, rfl⟩
  · rintro ⟨k, ⟨hk, hc⟩, rfl⟩
    refine ⟨⟨k, hk, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hc w hw]

theorem omegaOneOf_map {f : G₁ →* G₂} (hf : Function.Injective f) (K : Subgroup G₁) :
    omegaOneOf (K.map f) = (omegaOneOf K).map f := by
  unfold omegaOneOf
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hx⟩
    exact ⟨k, ⟨hk, hf (by rw [map_pow, map_one]; exact hx)⟩, rfl⟩
  · rintro ⟨k, ⟨hk, hk2⟩, rfl⟩
    exact ⟨⟨k, hk, rfl⟩, by rw [← map_pow, hk2, map_one]⟩

theorem omegaOneCenterOf_map {f : G₁ →* G₂} (hf : Function.Injective f) (K : Subgroup G₁) :
    omegaOneCenterOf (K.map f) = (omegaOneCenterOf K).map f := by
  unfold omegaOneCenterOf
  rw [centerOf_map hf, omegaOneOf_map hf]

theorem range_inf_centralizer_map {f : G₁ →* G₂} (hf : Function.Injective f) (K : Subgroup G₁) :
    f.range ⊓ Subgroup.centralizer (K.map f : Set G₂) =
      (Subgroup.centralizer (K : Set G₁)).map f := by
  ext x
  simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
    Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨y, rfl⟩, hc⟩
    refine ⟨y, fun w hw => hf ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hc (f w) ⟨w, hw, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hy w hw]

theorem centralizer_map_mulEquiv (e : G₁ ≃* G₂) (K : Subgroup G₁) :
    Subgroup.centralizer (K.map e.toMonoidHom : Set G₂) =
      (Subgroup.centralizer (K : Set G₁)).map e.toMonoidHom := by
  rw [← range_inf_centralizer_map (f := e.toMonoidHom) e.injective,
    MonoidHom.range_eq_top.mpr e.surjective, top_inf_eq]

theorem map_iInf_mulEquiv {ι : Sort*} (e : G₁ ≃* G₂) (H : ι → Subgroup G₁) :
    (⨅ i, H i).map e.toMonoidHom = ⨅ i, (H i).map e.toMonoidHom := by
  simp only [Subgroup.map_equiv_eq_comap_symm', Subgroup.comap_iInf]

theorem mem_map_conj {G : Type*} [Group G] {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_mul {G : Type*} [Group G] (K : Subgroup G) (g h : G) :
    K.map (MulAut.conj (g * h)).toMonoidHom =
      (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_conj, mem_map_conj, mem_map_conj]
  constructor <;> intro hx <;> convert hx using 1 <;> group

theorem map_conj_one {G : Type*} [Group G] (K : Subgroup G) :
    K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  rw [mem_map_conj, inv_one, one_mul, mul_one]

end Transport

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem treeGraph_connected : X.treeGraph.Connected :=
  X.treeGraph_isTree.connected

private theorem dist_smul_le (g : X.Universal) (u w : Vtx X) :
    X.treeGraph.dist (g • u) (g • w) ≤ X.treeGraph.dist u w := by
  obtain ⟨p, hp⟩ := (treeGraph_connected X).exists_walk_length_eq_dist u w
  let f : X.treeGraph →g X.treeGraph := ⟨(g • ·), fun h => (adj_smul X g _ _).2 h⟩
  calc X.treeGraph.dist (g • u) (g • w) ≤ (p.map f).length := SimpleGraph.dist_le _
    _ = X.treeGraph.dist u w := by rw [SimpleGraph.Walk.length_map, hp]

theorem dist_smul (g : X.Universal) (u w : Vtx X) :
    X.treeGraph.dist (g • u) (g • w) = X.treeGraph.dist u w := by
  refine le_antisymm (dist_smul_le X g u w) ?_
  have := dist_smul_le X g⁻¹ (g • u) (g • w)
  rwa [inv_smul_smul, inv_smul_smul] at this

theorem image_smul_setOf_dist (g : X.Universal) (δ : Vtx X) (p : ℕ → Prop) :
    (fun ρ => g • ρ) '' {ρ : Vtx X | p (X.treeGraph.dist δ ρ)} =
      {ρ : Vtx X | p (X.treeGraph.dist (g • δ) ρ)} := by
  ext ρ
  constructor
  · rintro ⟨ρ', hρ', rfl⟩
    show p (X.treeGraph.dist (g • δ) (g • ρ'))
    rw [dist_smul]
    exact hρ'
  · intro hρ
    refine ⟨g⁻¹ • ρ, ?_, smul_inv_smul g ρ⟩
    show p (X.treeGraph.dist δ (g⁻¹ • ρ))
    rw [← dist_smul X g, smul_inv_smul]
    exact hρ

theorem neighborSet_smul (g : X.Universal) (δ : Vtx X) :
    X.treeGraph.neighborSet (g • δ) = (fun ρ => g • ρ) '' X.treeGraph.neighborSet δ := by
  ext ρ
  simp only [SimpleGraph.mem_neighborSet, Set.mem_image]
  constructor
  · intro h
    refine ⟨g⁻¹ • ρ, ?_, smul_inv_smul g ρ⟩
    exact (adj_smul X g δ (g⁻¹ • ρ)).1 (by rwa [smul_inv_smul])
  · rintro ⟨ρ', h, rfl⟩
    exact (adj_smul X g δ ρ').2 h

theorem isMVtx_baseA : IsMVtx X (baseA X) := rfl

theorem not_isMVtx_baseB : ¬ IsMVtx X (baseB X) := by
  simp [IsMVtx, baseB, GoldAmalgam.vtx]

theorem isMVtx_smul (g : X.Universal) (δ : Vtx X) : IsMVtx X (g • δ) ↔ IsMVtx X δ := by
  rcases δ with q | q <;> rfl

theorem isMVtx_iff {δ : Vtx X} : IsMVtx X δ ↔ ∃ g : X.Universal, δ = g • baseA X := by
  constructor
  · intro h
    rcases exists_smul_base X δ with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact ⟨g, rfl⟩
    · exact absurd ((isMVtx_smul X g _).1 h) (not_isMVtx_baseB X)
  · rintro ⟨g, rfl⟩
    exact (isMVtx_smul X g _).2 (isMVtx_baseA X)

theorem not_isMVtx_iff {δ : Vtx X} : ¬ IsMVtx X δ ↔ ∃ g : X.Universal, δ = g • baseB X := by
  constructor
  · intro h
    rcases exists_smul_base X δ with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact absurd ((isMVtx_smul X g _).2 (isMVtx_baseA X)) h
    · exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    rw [isMVtx_smul]
    exact not_isMVtx_baseB X

theorem mem_stab_iff {δ : Vtx X} {g : X.Universal} : g ∈ stab X δ ↔ g • δ = δ :=
  MulAction.mem_stabilizer_iff

theorem mem_kerAt_iff {δ : Vtx X} {i : ℕ} {g : X.Universal} :
    g ∈ kerAt X δ i ↔ ∀ ρ, X.treeGraph.dist δ ρ ≤ i → g • ρ = ρ := by
  simp [kerAt, stab, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

theorem mem_qv_iff {δ : Vtx X} {g : X.Universal} :
    g ∈ Qv X δ ↔ g • δ = δ ∧ ∀ ρ, X.treeGraph.Adj δ ρ → g • ρ = ρ := by
  rw [Qv, mem_kerAt_iff]
  constructor
  · intro h
    exact ⟨h δ (by simp), fun ρ hρ => h ρ (SimpleGraph.dist_eq_one_iff_adj.2 hρ).le⟩
  · rintro ⟨h0, h1⟩ ρ hρ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hρ with h | h
    · rw [(treeGraph_connected X).dist_eq_zero_iff] at h
      exact h ▸ h0
    · exact h1 ρ (SimpleGraph.dist_eq_one_iff_adj.1 h)

theorem qv_le_stab (δ : Vtx X) : Qv X δ ≤ stab X δ := fun _ hg =>
  (mem_stab_iff X).2 ((mem_qv_iff X).1 hg).1

theorem qv_le_stab_of_adj {δ ρ : Vtx X} (h : X.treeGraph.Adj δ ρ) : Qv X δ ≤ stab X ρ :=
  fun _ hg => (mem_stab_iff X).2 (((mem_qv_iff X).1 hg).2 ρ h)

theorem eq_one_of_forall_smul_eq (hf : X.IsFaithful) {g : X.Universal}
    (hg : ∀ v : Vtx X, g • v = v) : g = 1 := by
  have hf' := (X.universalCompletion.isFaithful_iff_ker_inf_ker_eq_bot).1 hf
  have hmem : g ∈ (MulAction.toPermHom X.Universal
        (X.Universal ⧸ X.universalCompletion.ψA.range)).ker ⊓
      (MulAction.toPermHom X.Universal (X.Universal ⧸ X.universalCompletion.ψB.range)).ker :=
    ⟨MonoidHom.mem_ker.2 (Equiv.ext fun q => Sum.inl_injective (hg (Sum.inl q))),
      MonoidHom.mem_ker.2 (Equiv.ext fun q => Sum.inr_injective (hg (Sum.inr q)))⟩
  rw [hf'] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem eq_bot_of_le_qv (hf : X.IsFaithful) {K : Subgroup X.Universal}
    (hK : ∀ δ : Vtx X, K ≤ Qv X δ) : K = ⊥ := by
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  exact eq_one_of_forall_smul_eq X hf fun v => (mem_stab_iff X).1 (qv_le_stab X v (hK v hk))

theorem stab_smul (g : X.Universal) (δ : Vtx X) :
    stab X (g • δ) = (stab X δ).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g δ

theorem kerAt_smul (g : X.Universal) (δ : Vtx X) (i : ℕ) :
    kerAt X (g • δ) i = (kerAt X δ i).map (MulAut.conj g).toMonoidHom := by
  rw [kerAt, kerAt, ← image_smul_setOf_dist X g δ (· ≤ i), iInf_image]
  simp only [map_iInf_mulEquiv, stab_smul]

theorem qv_smul (g : X.Universal) (δ : Vtx X) :
    Qv X (g • δ) = (Qv X δ).map (MulAut.conj g).toMonoidHom :=
  kerAt_smul X g δ 1

theorem zh_smul (g : X.Universal) (δ : Vtx X) :
    ZH X (g • δ) = (ZH X δ).map (MulAut.conj g).toMonoidHom := by
  rw [ZH, ZH, qv_smul, omegaOneCenterOf_map (MulAut.conj g).injective]

theorem zm_smul (g : X.Universal) (δ : Vtx X) :
    ZM X (g • δ) = (ZM X δ).map (MulAut.conj g).toMonoidHom := by
  rw [ZM, ZM, neighborSet_smul, iSup_image]
  simp only [Subgroup.map_iSup, zh_smul]

theorem zv_smul (g : X.Universal) (δ : Vtx X) :
    Zv X (g • δ) = (Zv X δ).map (MulAut.conj g).toMonoidHom := by
  by_cases h : IsMVtx X δ
  · rw [zv_of_isMVtx X h, zv_of_isMVtx X ((isMVtx_smul X g δ).2 h), zm_smul]
  · rw [zv_of_not_isMVtx X h, zv_of_not_isMVtx X (fun h' => h ((isMVtx_smul X g δ).1 h')),
      zh_smul]

theorem vi_smul (g : X.Universal) (δ : Vtx X) (i : ℕ) :
    Vi X (g • δ) i = (Vi X δ i).map (MulAut.conj g).toMonoidHom := by
  rw [Vi, Vi, ← image_smul_setOf_dist X g δ (· ≤ i), iSup_image]
  simp only [Subgroup.map_iSup, zv_smul]

theorem xm_smul (g : X.Universal) (δ : Vtx X) :
    XM X (g • δ) = (XM X δ).map (MulAut.conj g).toMonoidHom := by
  rw [XM, XM, qv_smul, omegaOneCenterOf_map (MulAut.conj g).injective]

theorem stab_le_normalizer_of_smul {F : Vtx X → Subgroup X.Universal}
    (hF : ∀ (g : X.Universal) (δ : Vtx X), F (g • δ) = (F δ).map (MulAut.conj g).toMonoidHom)
    (δ : Vtx X) : stab X δ ≤ Subgroup.normalizer (F δ : Set X.Universal) := by
  intro g hg
  have hgδ : g • δ = δ := (mem_stab_iff X).1 hg
  have hFg : F δ = (F δ).map (MulAut.conj g).toMonoidHom := by
    have := hF g δ
    rwa [hgδ] at this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  conv_rhs => rw [hFg, mem_map_conj]
  constructor <;> intro hh <;> convert hh using 1 <;> group

end CFSG.Quasithin.MS93.PU
