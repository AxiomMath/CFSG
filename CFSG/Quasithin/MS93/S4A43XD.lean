module

public import CFSG.Quasithin.MS93.S4A43XC

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Hol

variable {G : Type} [Group G] [Finite G] {M T : Subgroup G} (hTM : T ≤ M)

theorem exists_stab_conj_eq_baseB {g : (puAmalgam hTM).Universal}
    (hg : g ∈ Subgroup.normalizer (Qv (puAmalgam hTM) (baseB _) : Set _)) :
    ∃ k ∈ stab (puAmalgam hTM) (baseB _), ∀ t ∈ Qv (puAmalgam hTM) (baseB _),
      g * t * g⁻¹ = k * t * k⁻¹ := by
  set f := puAmalgam.ofT hTM with hf
  have hQ : Qv (puAmalgam hTM) (baseB _) = f.range := by
    rw [puAmalgam.qv_baseB, imM_T, hf, puAmalgam.ofT, MonoidHom.range_comp]
  have hinj : Function.Injective f :=
    (puAmalgam hTM).ofB_injective.comp SemidirectProduct.inl_injective
  have hmem : ∀ t : ↥T, g * f t * g⁻¹ ∈ f.range := fun t => by
    rw [← hQ]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp (hQ ▸ ⟨t, rfl⟩)
  choose φ hφ using hmem
  have hφmul : ∀ a b, φ (a * b) = φ a * φ b := fun a b =>
    hinj (by rw [map_mul, hφ, hφ, hφ, map_mul]; group)
  have hφinj : Function.Injective φ := fun a b hab => by
    have := congrArg f hab
    rw [hφ, hφ] at this
    exact hinj (mul_left_cancel (mul_right_cancel this))
  let ψ : MulAut ↥T :=
    MulEquiv.ofBijective (MonoidHom.mk' φ hφmul) ⟨hφinj, Finite.injective_iff_surjective.mp hφinj⟩
  refine ⟨(puAmalgam hTM).ofB (SemidirectProduct.inr ψ), ?_, ?_⟩
  · rw [puAmalgam.stab_baseB]
    exact ⟨_, rfl⟩
  · intro t ht
    rw [hQ] at ht
    obtain ⟨t, rfl⟩ := ht
    have e : (puAmalgam hTM).ofB (SemidirectProduct.inr ψ) * f t *
        ((puAmalgam hTM).ofB (SemidirectProduct.inr ψ))⁻¹ = f (ψ t) := by
      rw [hf, puAmalgam.ofT]
      simp only [MonoidHom.comp_apply]
      rw [← map_inv, ← map_mul, ← map_mul, Hol.inr_mul_inl_mul_inr_inv]
    rw [e, ← hφ t]
    rfl

theorem exists_stab_conj_eq {ρ : Vtx (puAmalgam hTM)} (hρ : ¬ IsMVtx (puAmalgam hTM) ρ)
    {g : (puAmalgam hTM).Universal}
    (hg : g ∈ Subgroup.normalizer (Qv (puAmalgam hTM) ρ : Set _)) :
    ∃ k ∈ stab (puAmalgam hTM) ρ, ∀ t ∈ Qv (puAmalgam hTM) ρ, g * t * g⁻¹ = k * t * k⁻¹ := by
  obtain ⟨y, rfl⟩ := exists_eq_smul_baseB _ hρ
  rw [qv_smul, normalizer_map_conj, mem_map_conj] at hg
  obtain ⟨k₀, hk₀, hk₀t⟩ := exists_stab_conj_eq_baseB hTM hg
  refine ⟨y * k₀ * y⁻¹, ?_, fun t ht => ?_⟩
  · rw [stab_smul]
    exact conj_mem_map_conj hk₀
  · rw [qv_smul, mem_map_conj] at ht
    have := hk₀t _ ht
    calc g * t * g⁻¹ = y * ((y⁻¹ * g * y) * (y⁻¹ * t * y) * (y⁻¹ * g * y)⁻¹) * y⁻¹ := by group
      _ = y * (k₀ * (y⁻¹ * t * y) * k₀⁻¹) * y⁻¹ := by rw [this]
      _ = (y * k₀ * y⁻¹) * t * (y * k₀ * y⁻¹)⁻¹ := by group

theorem exists_centralizer_smul_eq {ρ : Vtx (puAmalgam hTM)} (hρ : ¬ IsMVtx (puAmalgam hTM) ρ)
    {g : (puAmalgam hTM).Universal}
    (hg : g ∈ Subgroup.normalizer (Qv (puAmalgam hTM) ρ : Set _)) :
    ∃ c ∈ Subgroup.centralizer ((Qv (puAmalgam hTM) ρ : Subgroup _) :
      Set (puAmalgam hTM).Universal), c • ρ = g • ρ := by
  obtain ⟨k, hk, hkt⟩ := exists_stab_conj_eq hTM hρ hg
  refine ⟨g * k⁻¹, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_, ?_⟩
  · have hs : k⁻¹ * t * k ∈ Qv (puAmalgam hTM) ρ :=
      (Subgroup.mem_normalizer_iff.mp
        (stab_le_normalizer_qv _ ρ (Subgroup.inv_mem _ hk)) t).mp ht |> fun h => by
          simpa using h
    have h1 := hkt _ hs
    have e1 : (g * k⁻¹) * t * (g * k⁻¹)⁻¹ = t := by
      calc (g * k⁻¹) * t * (g * k⁻¹)⁻¹ = g * (k⁻¹ * t * k) * g⁻¹ := by group
        _ = t := by rw [h1]; group
    calc t * (g * k⁻¹) = ((g * k⁻¹) * t * (g * k⁻¹)⁻¹) * (g * k⁻¹) := by rw [e1]
      _ = (g * k⁻¹) * t := by group
  · rw [mul_smul, (mem_stab _).mp (Subgroup.inv_mem _ hk)]

end Hol

section Wnab

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)

theorem wnab_smul (g : (puAmalgam h.le).Universal) (α ρ : Vtx (puAmalgam h.le)) :
    Wnab h.le L (g • α) (g • ρ) = (Wnab h.le L α ρ).map (MulAut.conj g).toMonoidHom := by
  rw [Wnab, Wnab, Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun μ hμ => ?_
    have hμ' : g⁻¹ • μ ∈ {μ : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.Adj ρ μ ∧
        α ∈ nablaSet h.le L μ} := by
      refine ⟨?_, ?_⟩
      · have := (adj_smul _ g⁻¹ _ _).mpr hμ.1
        rwa [inv_smul_smul] at this
      · have := (mem_nablaSet_smul h g⁻¹ μ (g • α)).mpr hμ.2
        rwa [inv_smul_smul] at this
    refine le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.Adj ρ μ ∧ α ∈ nablaSet h.le L μ}) =>
      (Vv (puAmalgam h.le) μ).map (MulAut.conj g).toMonoidHom) (g⁻¹ • μ) hμ' ?_
    rw [← vi_smul, smul_inv_smul]
  · refine iSup₂_le fun μ hμ => ?_
    have hμ' : g • μ ∈ {μ : Vtx (puAmalgam h.le) |
        (puAmalgam h.le).treeGraph.Adj (g • ρ) μ ∧ g • α ∈ nablaSet h.le L μ} :=
      ⟨(adj_smul _ g _ _).mpr hμ.1, (mem_nablaSet_smul h g μ α).mpr hμ.2⟩
    refine le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.Adj (g • ρ) μ ∧ g • α ∈ nablaSet h.le L μ}) =>
      Vv (puAmalgam h.le) μ) (g • μ) hμ' ?_
    rw [← vi_smul]

theorem mem_nablaSet_iff_of_adj (hb : 2 < critDist (puAmalgam h.le))
    {x y μ : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) (hyx : (puAmalgam h.le).treeGraph.Adj y x)
    (hyμ : (puAmalgam h.le).treeGraph.Adj y μ) :
    x ∈ nablaSet h.le L μ ↔ ¬ ZM (puAmalgam h.le) x ≤ Bloc h.le L μ := by
  rw [nablaSet, Set.mem_ofPred_eq, zv_of_isMVtx _ hx]
  by_cases hxμ : μ = x
  · subst hxμ
    simp only [SimpleGraph.dist_self, OfNat.zero_ne_ofNat, false_and, false_iff, not_not]
    exact zm_le_bloc h hb hx
  · simp [dist_eq_two_of_adj_adj _ hyμ.symm hyx (Ne.symm (Ne.symm hxμ))]

theorem gab_le_normalizer_wnab (hb : 3 < critDist (puAmalgam h.le)) {α ρ : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hαρ : (puAmalgam h.le).treeGraph.Adj α ρ) :
    Gab (puAmalgam h.le) α ρ ≤
      Subgroup.normalizer (Wnab h.le L α ρ : Set (puAmalgam h.le).Universal) := by
  have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by rw [← isMVtx_iff_of_adj _ hαρ]; exact hα
  have hWQ : Wnab h.le L α ρ ≤ Qv (puAmalgam h.le) ρ := iSup₂_le fun μ hμ => by
    have hμM : IsMVtx (puAmalgam h.le) μ := by have := isMVtx_iff_of_adj _ hμ.1; tauto
    exact vv_le_qv_of_dist h hμM (by rw [dist_eq_one_of_adj _ hμ.1.symm]; omega)
  refine le_normalizer_of_map_conj_le fun g hg => le_of_eq ?_
  obtain ⟨hgα, hgN⟩ := hg
  obtain ⟨c, hc, hcρ⟩ := exists_centralizer_smul_eq h.le hρH hgN
  have hgα' : g • α = α := (mem_stab _).mp hgα
  have hcW : (Wnab h.le L α ρ).map (MulAut.conj c).toMonoidHom = Wnab h.le L α ρ :=
    map_conj_eq_of_le_centralizer (Subgroup.le_centralizer_iff.mpr (Subgroup.centralizer_le hWQ))
      hc
  have hZc : ZM (puAmalgam h.le) (c • α) = ZM (puAmalgam h.le) α := by
    rw [zm_smul]
    exact map_conj_eq_of_le_centralizer (Subgroup.le_centralizer_iff.mpr (Subgroup.centralizer_le
      ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_qv _ h.hyp20 hα hαρ)))) hc
  have hαg : (puAmalgam h.le).treeGraph.Adj (g • ρ) α := by
    have := (adj_smul _ g _ _).mpr hαρ
    rw [hgα'] at this
    exact this.symm
  have hcαg : (puAmalgam h.le).treeGraph.Adj (g • ρ) (c • α) := by
    have := (adj_smul _ c _ _).mpr hαρ
    rw [hcρ] at this
    exact this.symm
  have hcαM : IsMVtx (puAmalgam h.le) (c • α) := (isMVtx_smul _ c α).mpr hα
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hS : {μ | (puAmalgam h.le).treeGraph.Adj (g • ρ) μ ∧ c • α ∈ nablaSet h.le L μ} =
      {μ | (puAmalgam h.le).treeGraph.Adj (g • ρ) μ ∧ α ∈ nablaSet h.le L μ} := by
    ext μ
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hμ, hn⟩
      refine ⟨hμ, (mem_nablaSet_iff_of_adj h hb2 hα hαg hμ).mpr ?_⟩
      rw [← hZc]
      exact (mem_nablaSet_iff_of_adj h hb2 hcαM hcαg hμ).mp hn
    · rintro ⟨hμ, hn⟩
      refine ⟨hμ, (mem_nablaSet_iff_of_adj h hb2 hcαM hcαg hμ).mpr ?_⟩
      rw [hZc]
      exact (mem_nablaSet_iff_of_adj h hb2 hα hαg hμ).mp hn
  calc (Wnab h.le L α ρ).map (MulAut.conj g).toMonoidHom = Wnab h.le L α (g • ρ) := by
        rw [← wnab_smul h, hgα']
    _ = Wnab h.le L (c • α) (g • ρ) := by
        simp only [Wnab]
        rw [hS]
    _ = Wnab h.le L α ρ := by rw [← hcρ, wnab_smul h, hcW]

end Wnab

section Kernel

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem commutator_ltil_le_of_comm_le {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {N X W₀ : Subgroup (puAmalgam h.le).Universal}
    (hNn : stab _ α ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal))
    (hXβ : X ≤ Qv _ β) (hXα : ¬ X ≤ Qv _ α)
    (hW₀ : stab _ α ≤ Subgroup.normalizer (W₀ : Set (puAmalgam h.le).Universal))
    (hXW : ⁅N, X⁆ ≤ W₀) :
    ⁅N, Ltil h.le L α⁆ ≤ W₀ := by
  let K : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {g | g ∈ stab (puAmalgam h.le) α ∧ ∀ v ∈ N, ⁅v, g⁆ ∈ W₀}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun v hv => ?_⟩
        have hrw : ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [hrw]
        exact Subgroup.mul_mem _ (ha' v hv) ((Subgroup.mem_normalizer_iff.mp (hW₀ ha) _).mp
          (hb' v hv))
      one_mem' := ⟨Subgroup.one_mem _, fun v _ => by
        rw [commutatorElement_one_right]
        exact Subgroup.one_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun v hv => ?_⟩
        have hrw : ⁅v, a⁻¹⁆ = a⁻¹ * (⁅v, a⁆)⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [hrw]
        exact (Subgroup.mem_normalizer_iff.mp (hW₀ (Subgroup.inv_mem _ ha)) _).mp
          (Subgroup.inv_mem _ (ha' v hv)) }
  have hKs : K ≤ stab (puAmalgam h.le) α := fun g hg => hg.1
  have hKn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (K : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun s hs => ?_
    rintro _ ⟨k, ⟨hk, hk'⟩, rfl⟩
    refine ⟨?_, fun v hv => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hk) (Subgroup.inv_mem _ hs)
    · have hv' : s⁻¹ * v * s⁻¹⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hNn (Subgroup.inv_mem _ hs)) _).mp hv
      have hrw : ⁅v, (MulAut.conj s).toMonoidHom k⁆ = s * ⁅s⁻¹ * v * s⁻¹⁻¹, k⁆ * s⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [hrw]
      exact (Subgroup.mem_normalizer_iff.mp (hW₀ hs) _).mp (hk' _ hv')
  have hXK : X ≤ K := fun x hx =>
    ⟨qv_le_stab_of_adj _ hαβ.symm (hXβ hx), fun v hv =>
      hXW (Subgroup.commutator_mem_commutator hv hx)⟩
  have hLs := ltil_le_stab h α
  have hJL : ⁅K, Ltil h.le L α⁆ ≤ Ltil h.le L α := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hKs.trans (stab_le_normalizer_ltil h α))
  have hJK : ⁅K, Ltil h.le L α⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hKn)
  rcases commutator_ltil_le_or h hα hJL (Subgroup.normalizer_commutator_ge_right _ _) with hc | hc
  · exfalso
    apply hXα
    have hO : pCoreLtil h α ≤ Qv _ α := pCoreLtil_le_qv h hα
    have hQn : stab (puAmalgam h.le) α ≤
        Subgroup.normalizer (Qv (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
      stab_le_normalizer_qv _ α
    have h3 : ⁅⁅Ltil h.le L α, Ltil h.le L α⁆, K⁆ ≤ Qv _ α := by
      refine three_subgroups_le (hLs.trans hQn) (hLs.trans hQn) (hKs.trans hQn) ?_ ?_
      · rw [Subgroup.commutator_comm (Ltil h.le L α) K]
        exact hc.trans hO
      · exact hc.trans hO
    rw [ltil_perfect h hα, Subgroup.commutator_comm] at h3
    exact le_qv_of_commutator_le h hfull hα hαβ hXβ
      ((Subgroup.commutator_mono hXK le_rfl).trans h3)
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    exact (hJK (hc hl)).2 v hv

omit hfull in
theorem commutator_ltil_le_vcirc {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    {N : Subgroup (puAmalgam h.le).Universal} (hN : N ≤ stab _ α)
    (hNV : ⁅N, Ltil h.le L α⁆ ≤ Vv (puAmalgam h.le) α) :
    ⁅N, Ltil h.le L α⁆ ≤ Vcirc h.le L α := by
  have hVn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Vcirc h.le L α : Set (puAmalgam h.le).Universal) :=
    le_normalizer_commutator (stab_le_normalizer_vv h α) (stab_le_normalizer_ltil h α)
  have hLs := ltil_le_stab h α
  have h1 : ⁅⁅N, Ltil h.le L α⁆, Ltil h.le L α⁆ ≤ Vcirc h.le L α :=
    Subgroup.commutator_mono hNV le_rfl
  have h3 := three_subgroups_le (N := Vcirc h.le L α) (H₁ := Ltil h.le L α)
    (H₂ := Ltil h.le L α) (H₃ := N) (hLs.trans hVn) (hLs.trans hVn) (hN.trans hVn)
    (by rw [Subgroup.commutator_comm (Ltil h.le L α) N]; exact h1) h1
  rw [ltil_perfect h hα, Subgroup.commutator_comm] at h3
  exact h3

end Kernel

end CFSG.Quasithin.MS93.S4A
