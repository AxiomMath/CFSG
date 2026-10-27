module

public import CFSG.Quasithin.MS93.Sec2Two

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph

open scoped commutatorElement

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem stab_le_normalizer_map_iff (g : X.Universal) (δ : Vtx X) (K : Subgroup X.Universal) :
    stab X (g • δ) ≤ Subgroup.normalizer
        ((K.map (MulAut.conj g).toMonoidHom : Subgroup X.Universal) : Set X.Universal) ↔
      stab X δ ≤ Subgroup.normalizer (K : Set X.Universal) := by
  rw [stab_smul, normalizer_map_conj, map_conj_le_map_conj_iff]

theorem qv_le_normalizer_map_iff (g : X.Universal) (δ : Vtx X) (K : Subgroup X.Universal) :
    Qv X (g • δ) ≤ Subgroup.normalizer
        ((K.map (MulAut.conj g).toMonoidHom : Subgroup X.Universal) : Set X.Universal) ↔
      Qv X δ ≤ Subgroup.normalizer (K : Set X.Universal) := by
  rw [qv_smul, normalizer_map_conj, map_conj_le_map_conj_iff]

theorem dist_smul_of_smul_eq {g : X.Universal} {u w : Vtx X} (hw : g • w = w) :
    X.treeGraph.dist (g • u) w = X.treeGraph.dist u w := by
  calc X.treeGraph.dist (g • u) w = X.treeGraph.dist (g • u) (g • w) := by rw [hw]
    _ = X.treeGraph.dist u w := dist_smul X g u w

theorem geo_one_eq_of_adj {x y z : Vtx X} {n : ℕ} (hxy : X.treeGraph.Adj x y)
    (hxz : X.treeGraph.dist x z = n + 1) (hyz : X.treeGraph.dist y z ≤ n) : geo X x z 1 = y := by
  have := dist_triangle X x y z
  rw [dist_eq_one_of_adj X hxy] at this
  exact (eq_geo_one X hxy (by omega)).symm

theorem xm_le_qv_geo_one (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X) {γ γ' : Vtx X}
    (hc : IsCritical X γ γ') : XM X γ' ≤ Qv X (geo X γ γ' 1) := by
  have hd : X.treeGraph.dist γ γ' = critDist X := hc.2.1
  have hb2 := two_le_critDist X h hb
  have h1 : X.treeGraph.Adj (geo X γ γ' 1) (geo X γ γ' 2) := adj_geo X (i := 1) (by omega)
  refine (ms22_i X h hC (hc.isMVtx_right X h) (isMVtx_geo_two X h hb hc) ?_).trans
    (qv_le_qv X h (isMVtx_geo_two X h hb hc) h1.symm)
  rw [SimpleGraph.dist_comm, dist_geo_right X (by omega), hd]
  omega

theorem xm_le_stab_of_isCritical (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
    {γ γ' : Vtx X} (hc : IsCritical X γ γ') : XM X γ ≤ stab X γ' := by
  have hc' := ms22_iii X h hb hC hc
  exact (xm_le_qv_geo_one X h hb hC hc').trans
    (qv_le_stab_of_adj X (adj_geo_one_of_isCritical X hb hc').symm)

theorem commutator_xm_le_right (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
    {γ γ' : Vtx X} (hc : IsCritical X γ γ') : ⁅XM X γ, XM X γ'⁆ ≤ XM X γ' :=
  Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((xm_le_stab_of_isCritical X h hb hC hc).trans (stab_le_normalizer_xm X γ'))

theorem le_normalizer_sup_of_commutator_le {G : Type*} [Group G] {Z Y W : Subgroup G}
    (hW : Z ≤ Subgroup.normalizer (W : Set G)) (hY : ⁅Y, Z⁆ ≤ Y ⊔ W) :
    Z ≤ Subgroup.normalizer ((Y ⊔ W : Subgroup G) : Set G) := by
  refine le_normalizer_of_map_conj_le fun z hz => ?_
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hW hz)]
  refine sup_le ?_ le_sup_right
  rintro _ ⟨y, hy, rfl⟩
  have e : (MulAut.conj z).toMonoidHom y = ⁅z, y⁆ * y := by
    simp [commutatorElement_def]
  rw [e]
  refine Subgroup.mul_mem _ (hY ?_) (Subgroup.mem_sup_left hy)
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hz hy

@[expose] def Gen23At (γ ρ : Vtx X) : Prop :=
  ∀ x ∈ Qv X ρ, x ∉ Qv X γ →
    stab X γ = Subgroup.closure {y | ∃ k ∈ stab X γ, k * x * k⁻¹ = y} ⊔ Qv X ρ

@[expose] def Zc23At (γ γ' : Vtx X) (Z : Subgroup X.Universal) : Prop :=
  Z ≤ XM X γ' ∧ ¬ Z ≤ Qv X γ ∧ ∀ Y : Subgroup X.Universal, Y ≤ Qv X (geo X γ' γ 1) →
    CFSG.Open.IsElemAbelian 2 (Y ⊔ XM X γ) →
      ⁅Y, Z⁆ ≤ ⁅XM X γ, XM X γ'⁆ ⊔ ⁅Y, XM X γ' ⊓ Qv X γ⁆

private theorem closure_conj_map (g x : X.Universal) (δ : Vtx X) :
    (Subgroup.closure {y | ∃ k ∈ stab X δ, k * x * k⁻¹ = y}).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure {y | ∃ k ∈ stab X (g • δ), k * (g * x * g⁻¹) * k⁻¹ = y} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · rw [mem_stab_smul]
      simpa [mul_assoc] using hk
    · simp [mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(g⁻¹ * k * g) * x * (g⁻¹ * k * g)⁻¹, ⟨g⁻¹ * k * g, (mem_stab_smul X).mp hk, rfl⟩, ?_⟩
    simp [mul_assoc]

theorem gen23At_smul {γ ρ : Vtx X} (hG : Gen23At X γ ρ) (g : X.Universal) :
    Gen23At X (g • γ) (g • ρ) := by
  intro x hx hxγ
  rw [qv_smul, mem_map_conj] at hx hxγ
  have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) (hG _ hx hxγ)
  rw [Subgroup.map_sup, closure_conj_map, ← stab_smul, ← qv_smul,
    show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  exact this

theorem zc23At_smul {γ γ' : Vtx X} {Z : Subgroup X.Universal} (hZ : Zc23At X γ γ' Z)
    (g : X.Universal) : Zc23At X (g • γ) (g • γ') (Z.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := hZ
  refine ⟨?_, ?_, fun Y hY hYe => ?_⟩
  · rw [xm_smul]
    exact Subgroup.map_mono h1
  · rwa [qv_smul, map_conj_le_map_conj_iff]
  · set Y' := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY'def
    have hYY : Y = Y'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv Y g).symm
    have hY' : Y' ≤ Qv X (geo X γ' γ 1) := by
      rw [geo_smul, qv_smul] at hY
      rw [hY'def, map_conj_le_iff, inv_inv]
      exact hY
    have hY'e : CFSG.Open.IsElemAbelian 2 (Y' ⊔ XM X γ) := by
      have e : Y' ⊔ XM X γ = (Y ⊔ XM X (g • γ)).map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [Subgroup.map_sup, xm_smul, map_conj_map_conj, inv_mul_cancel, map_conj_one]
      rw [e]
      exact (isElemAbelian_map_mulEquiv _).mpr hYe
    have key := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (h3 Y' hY' hY'e)
    rw [Subgroup.map_commutator, ← hYY, Subgroup.map_sup, Subgroup.map_commutator,
      Subgroup.map_commutator, ← hYY, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ← xm_smul, ← xm_smul, ← qv_smul] at key
    exact key

theorem ms23_step1 (h : Hyp20 X) {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β)
    (hG : Gen23At X α β) : CentHyp X := by
  refine centHyp_of_edge X hα hαβ (le_antisymm ?_ (le_inf (qv_le_qv X h hα hαβ)
    (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv X h hα))))
  rintro x ⟨hxβ, hxc⟩
  by_contra hxα
  have hgen := hG x hxβ hxα
  have hβ : ¬ IsMVtx X β := (isMVtx_iff_of_adj X hαβ).mp hα
  have hxCM : x ∈ CM X α := ⟨qv_le_stab_of_isMVtx X h hα hαβ hxβ, hxc⟩
  have hcl : Subgroup.closure {y | ∃ k ∈ stab X α, k * x * k⁻¹ = y} ≤ CM X α := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_of_smul X (cm_smul X) α hk) x).mp
      hxCM
  have hZβ : stab X α ≤ Subgroup.normalizer (ZH X β : Set X.Universal) := by
    rw [hgen]
    refine sup_le (hcl.trans ?_) ((qv_le_stab X β).trans (stab_le_normalizer_zh X β))
    exact inf_le_right.trans ((Subgroup.centralizer_le (zh_le_zm X hαβ)).trans
      (Subgroup.centralizer_le_normalizer _))
  exact zh_ne_bot X h hβ (ms21_iii X h hα hαβ (zh_le_qv X β) hZβ (stab_le_normalizer_zh X β))

theorem ms23_step2 (h : Hyp20 X) (hb : 0 < critDist X) (ha : 2 < critDist X) (hC : CentHyp X)
    (hG : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → Gen23At X γ ρ)
    {γ γ' : Vtx X} (hcr : IsCritical X γ γ') {Z : Subgroup X.Universal} (hZ : Zc23At X γ γ' Z)
    {N : Subgroup X.Universal}
    (hNT : Qv X (geo X γ γ' 1) ≤ Subgroup.normalizer (N : Set X.Universal))
    (hNG : ¬ stab X γ ≤ Subgroup.normalizer (N : Set X.Universal))
    {δ : Vtx X} (hδ : X.treeGraph.Adj (geo X γ γ' 1) δ)
    (hδN : ¬ stab X γ ≤ Subgroup.normalizer
      ((ZM X δ ⊔ XM X γ : Subgroup X.Universal) : Set X.Universal)) :
    ∃ g ∈ stab X γ, IsCritical X (g • δ) (geo X γ' γ 2) ∧
      ¬ Z ≤ Subgroup.normalizer
        ((N.map (MulAut.conj g).toMonoidHom : Subgroup X.Universal) : Set X.Universal) := by
  set ρ := geo X γ γ' 1
  have hd : X.treeGraph.dist γ γ' = critDist X := hcr.2.1
  have hγ : IsMVtx X γ := hcr.1
  have hγρ : X.treeGraph.Adj γ ρ := adj_geo_one_of_isCritical X hb hcr
  have hρ : ¬ IsMVtx X ρ := (isMVtx_iff_of_adj X hγρ).mp hγ
  have hδM : IsMVtx X δ := by
    have := isMVtx_iff_of_adj X hδ
    tauto
  obtain ⟨hZX, hZQ, hZc⟩ := hZ
  have hZρ : Z ≤ Qv X ρ := hZX.trans (xm_le_qv_geo_one X h hb hC hcr)
  have hργ : Qv X ρ ≤ stab X γ := qv_le_stab_of_isMVtx X h hγ hγρ
  have hZγ : Z ≤ stab X γ := hZρ.trans hργ
  obtain ⟨x, hxZ, hxQ⟩ := Set.not_subset.mp hZQ
  have hgen : stab X γ = (⨆ k ∈ stab X γ, Z.map (MulAut.conj k).toMonoidHom) ⊔ Qv X ρ := by
    refine le_antisymm ?_ (sup_le (iSup₂_le fun k hk => ?_) hργ)
    · calc stab X γ = Subgroup.closure {y | ∃ k ∈ stab X γ, k * x * k⁻¹ = y} ⊔ Qv X ρ :=
            hG γ ρ hγ hγρ x (hZρ hxZ) hxQ
        _ ≤ _ := by
          refine sup_le_sup_right ((Subgroup.closure_le _).mpr ?_) _
          rintro _ ⟨k, hk, rfl⟩
          exact (le_iSup₂_of_le k hk le_rfl : Z.map (MulAut.conj k).toMonoidHom ≤ _)
            (conj_mem_map_conj hxZ)
    · calc Z.map (MulAut.conj k).toMonoidHom ≤ (stab X γ).map (MulAut.conj k).toMonoidHom :=
            Subgroup.map_mono hZγ
        _ = stab X γ := map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hk)
  have hX₁T : Qv X ρ ≤ Subgroup.normalizer
      ((ZM X δ ⊔ XM X γ : Subgroup X.Universal) : Set X.Universal) :=
    le_normalizer_sup ((qv_le_stab_of_adj X hδ).trans (stab_le_normalizer_zm X δ))
      (hργ.trans (stab_le_normalizer_xm X γ))
  obtain ⟨g, hg, hg1, hg2⟩ := exists_conj_not_le_normalizer hgen hX₁T hδN hNT hNG
  refine ⟨g, hg, ?_, hg2⟩
  have hgγ : g • γ = γ := (mem_stab X).mp hg
  rw [Subgroup.map_sup, ← zm_smul, ← xm_smul, hgγ] at hg1
  set ε := geo X γ' γ 2
  set ν := geo X γ' γ 1
  have hcr' := ms22_iii X h hb hC hcr
  have hgδM : IsMVtx X (g • δ) := (isMVtx_smul X g δ).mpr hδM
  have hgδγ : X.treeGraph.dist (g • δ) γ ≤ 2 := by
    rw [dist_smul_of_smul_eq X hgγ]
    have := dist_triangle X δ ρ γ
    rw [dist_eq_one_of_adj X hδ.symm, dist_eq_one_of_adj X hγρ.symm] at this
    exact this
  have hγε : X.treeGraph.dist γ ε = critDist X - 2 := by
    rw [SimpleGraph.dist_comm, dist_geo_right X (by rw [SimpleGraph.dist_comm]; omega),
      SimpleGraph.dist_comm, hd]
  by_contra hncr
  apply hg1
  have hYε : ZM X (g • δ) ≤ Qv X ε := by
    by_cases hlt : X.treeGraph.dist (g • δ) ε < critDist X
    · exact zm_le_qv_of_dist_lt X hgδM hlt
    · by_contra hle
      have := dist_triangle X (g • δ) γ ε
      exact hncr ⟨hgδM, by omega, hle⟩
  have hνε : X.treeGraph.Adj ν ε := adj_geo X (i := 1) (by rw [SimpleGraph.dist_comm]; omega)
  have hεM : IsMVtx X ε := isMVtx_geo_two X h hb hcr'
  have hYν : ZM X (g • δ) ≤ Qv X ν := hYε.trans (qv_le_qv X h hεM hνε.symm)
  have hYγ : ZM X (g • δ) ≤ Qv X γ := zm_le_qv_of_dist_lt X hgδM (by omega)
  have hYe : CFSG.Open.IsElemAbelian 2 (ZM X (g • δ) ⊔ XM X γ) :=
    isElemAbelian_sup (isElemAbelian_zm X h hb hgδM) (isElemAbelian_xm X γ)
      (hYγ.trans (qv_le_centralizer_xm X γ))
  have hcomm := hZc _ hYν hYe
  have h1 : ⁅XM X γ, XM X γ'⁆ ≤ XM X γ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((xm_le_qv_geo_one X h hb hC hcr).trans hργ).trans (stab_le_normalizer_xm X γ))
  have h2 : ⁅ZM X (g • δ), XM X γ' ⊓ Qv X γ⁆ ≤ ZM X (g • δ) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp ((inf_le_right.trans
      (qv_le_stab_of_dist_le_two X h hγ (by rw [SimpleGraph.dist_comm]; exact hgδγ))).trans
        (stab_le_normalizer_zm X _))
  exact le_normalizer_sup_of_commutator_le ((hZγ.trans (stab_le_normalizer_xm X γ)))
    (hcomm.trans (sup_le (h1.trans le_sup_right) (h2.trans le_sup_left)))

theorem ms23_exists_adj_not_normal (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
    {γ γ' : Vtx X} (hcr : IsCritical X γ γ') :
    ∃ δ, X.treeGraph.Adj (geo X γ γ' 1) δ ∧ ¬ stab X γ ≤ Subgroup.normalizer
      ((ZM X δ ⊔ XM X γ : Subgroup X.Universal) : Set X.Universal) := by
  have hd : X.treeGraph.dist γ γ' = critDist X := hcr.2.1
  have hb2 := two_le_critDist X h hb
  have hγρ : X.treeGraph.Adj γ (geo X γ γ' 1) := adj_geo_one_of_isCritical X hb hcr
  have hργ₂ : X.treeGraph.Adj (geo X γ γ' 1) (geo X γ γ' 2) := adj_geo X (i := 1) (by omega)
  obtain ⟨k, hk, hkγ₂⟩ := exists_mem_stab_smul X hργ₂ hγρ.symm
  refine ⟨k • γ, ?_, ?_⟩
  · have := (adj_smul X k _ γ).mpr hγρ.symm
    rwa [(mem_stab X).mp hk] at this
  · have h4 := ms22_iv X h hb hC hcr
    rwa [← stab_le_normalizer_map_iff X k, Subgroup.map_sup, ← zm_smul, ← xm_smul, hkγ₂] at h4

theorem ms23_step3 (h : Hyp20 X) (hb : 0 < critDist X) (ha : 2 < critDist X) (hC : CentHyp X)
    (hG : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → Gen23At X γ ρ)
    (hZall : ∀ γ γ' : Vtx X, IsCritical X γ γ' → ∃ Z, Zc23At X γ γ' Z)
    {γ γ' : Vtx X} (hcr : IsCritical X γ γ') : ¬ Vv X γ ≤ Qv X (geo X γ' γ 2) := by
  obtain ⟨δ, hδ, hδN⟩ := ms23_exists_adj_not_normal X h hb hC hcr
  obtain ⟨Z, hZ⟩ := hZall γ γ' hcr
  have hγρ := adj_geo_one_of_isCritical X hb hcr
  obtain ⟨g, hg, hgc, -⟩ := ms23_step2 X h hb ha hC hG hcr hZ (N := Qv X (geo X γ γ' 1))
    Subgroup.le_normalizer (not_stab_le_normalizer_qv X h hcr.1 hγρ) hδ hδN
  intro hle
  apply hgc.2.2
  refine le_trans ?_ hle
  have hgd : X.treeGraph.dist γ (g • δ) ≤ 2 := by
    rw [SimpleGraph.dist_comm, dist_smul_of_smul_eq X ((mem_stab X).mp hg)]
    have := dist_triangle X δ (geo X γ γ' 1) γ
    rw [dist_eq_one_of_adj X hδ.symm, dist_eq_one_of_adj X hγρ.symm] at this
    exact this
  rw [← zv_of_isMVtx X hgc.1]
  exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist γ ρ ≤ 2}) => Zv X ρ)
    (g • δ) hgd le_rfl

theorem ms23 (h : Hyp20 X) {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β)
    (ha : 2 < critDist X)
    (hb : ∀ x ∈ Qv X β, x ∉ Qv X α →
      stab X α = Subgroup.closure {y | ∃ g ∈ stab X α, g * x * g⁻¹ = y} ⊔ Qv X β)
    (hc : ∀ α' : Vtx X, IsCritical X α α' → geo X α α' 1 = β → ∃ Z : Subgroup X.Universal,
      Z ≤ XM X α' ∧ ¬ Z ≤ Qv X α ∧ ∀ Y : Subgroup X.Universal, Y ≤ Qv X (geo X α' α 1) →
        CFSG.Open.IsElemAbelian 2 (Y ⊔ XM X α) →
          ⁅Y, Z⁆ ≤ ⁅XM X α, XM X α'⁆ ⊔ ⁅Y, XM X α' ⊓ Qv X α⁆)
    {Aαβ : Subgroup X.Universal}
    (hAT : Qv X β ≤ Subgroup.normalizer (Aαβ : Set X.Universal))
    (hAG : ¬ stab X α ≤ Subgroup.normalizer (Aαβ : Set X.Universal))
    (hAc : ∀ δ' : Vtx X, IsCritical X α δ' → geo X α δ' 1 = β → Aαβ ≤ ⁅XM X α, XM X δ'⁆) :
    critDist X = 4 ∧ ∀ α' : Vtx X, IsCritical X α α' → geo X α α' 1 = β →
      stab X (geo X α α' 2) ≤ Subgroup.normalizer (Aαβ : Set X.Universal) := by
  have hb0 : 0 < critDist X := by omega
  have hb2 := two_le_critDist X h hb0
  have hG : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → Gen23At X γ ρ := by
    intro γ ρ hγ hγρ
    obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx X hα hαβ hγ hγρ
    exact gen23At_smul X hb g
  have hC : CentHyp X := ms23_step1 X h hα hαβ hb
  have hZall : ∀ γ γ' : Vtx X, IsCritical X γ γ' → ∃ Z, Zc23At X γ γ' Z := by
    intro γ γ' hcr
    have hγρ := adj_geo_one_of_isCritical X hb0 hcr
    obtain ⟨g, hg1, hg2⟩ := exists_smul_edge_of_isMVtx X hα hαβ hcr.1 hγρ
    have hα' : α = g⁻¹ • γ := by rw [← hg1, inv_smul_smul]
    have hcr' : IsCritical X α (g⁻¹ • γ') := by
      rw [hα']
      exact (isCritical_smul X g⁻¹ γ γ').mpr hcr
    have hgeo : geo X α (g⁻¹ • γ') 1 = β := by
      rw [hα', geo_smul, ← hg2, inv_smul_smul]
    obtain ⟨Z, hZ⟩ := hc _ hcr' hgeo
    refine ⟨Z.map (MulAut.conj g).toMonoidHom, ?_⟩
    have := zc23At_smul X hZ g
    rwa [hg1, smul_inv_smul] at this
  have hV : ∀ δ δ' : Vtx X, IsCritical X δ δ' → ¬ Vv X δ ≤ Qv X (geo X δ' δ 2) :=
    fun δ δ' hcr => ms23_step3 X h hb0 ha hC hG hZall hcr
  have hAd : ∀ (g : X.Universal) (δ' : Vtx X), IsCritical X (g • α) δ' →
      geo X (g • α) δ' 1 = g • β →
        Aαβ.map (MulAut.conj g).toMonoidHom ≤ ⁅XM X (g • α), XM X δ'⁆ := by
    intro g δ' hcr hgeo
    have hcr' : IsCritical X α (g⁻¹ • δ') := by
      have := (isCritical_smul X g⁻¹ _ _).mpr hcr
      rwa [inv_smul_smul] at this
    have hgeo' : geo X α (g⁻¹ • δ') 1 = β := by
      calc geo X α (g⁻¹ • δ') 1 = geo X (g⁻¹ • (g • α)) (g⁻¹ • δ') 1 := by rw [inv_smul_smul]
        _ = g⁻¹ • geo X (g • α) δ' 1 := geo_smul X _ _ _ _
        _ = β := by rw [hgeo, inv_smul_smul]
    have key := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (hAc _ hcr' hgeo')
    rwa [Subgroup.map_commutator, ← xm_smul, ← xm_smul, smul_inv_smul] at key
  have step4 : ∀ α' : Vtx X, IsCritical X α α' → geo X α α' 1 = β →
      stab X (geo X α α' 2) ≤ Subgroup.normalizer (Aαβ : Set X.Universal) := by
    intro α' hcr hβ
    have hd : X.treeGraph.dist α α' = critDist X := hcr.2.1
    have hα' := hcr.isMVtx_right X h
    set γ₂ := geo X α α' 2
    have hβγ₂ : X.treeGraph.Adj β γ₂ := hβ ▸ adj_geo X (i := 1) (by omega)
    obtain ⟨k, hk, hkγ₂⟩ := exists_mem_stab_smul X hβγ₂ hαβ.symm
    have hkβ : k • β = β := (mem_stab X).mp hk
    set δ := k • α
    have hδ : X.treeGraph.Adj β δ := by
      have := (adj_smul X k β α).mpr hαβ.symm
      rwa [hkβ] at this
    have hδN : ¬ stab X α ≤ Subgroup.normalizer
        ((ZM X δ ⊔ XM X α : Subgroup X.Universal) : Set X.Universal) := by
      have h4 := ms22_iv X h hb0 hC hcr
      rwa [← stab_le_normalizer_map_iff X k, Subgroup.map_sup, ← zm_smul, ← xm_smul, hkγ₂] at h4
    by_contra hN
    have hN' : ¬ stab X α ≤ Subgroup.normalizer
        ((Aαβ.map (MulAut.conj k).toMonoidHom : Subgroup X.Universal) : Set X.Universal) := by
      rwa [← hkγ₂, stab_le_normalizer_map_iff]
    have hNT : Qv X (geo X α α' 1) ≤ Subgroup.normalizer
        ((Aαβ.map (MulAut.conj k).toMonoidHom : Subgroup X.Universal) : Set X.Universal) := by
      rw [hβ, ← hkβ, qv_le_normalizer_map_iff]
      exact hAT
    obtain ⟨Z, hZ⟩ := hZall α α' hcr
    obtain ⟨g, hg, hgc, hgZ⟩ := ms23_step2 X h hb0 ha hC hG hcr hZ hNT hN' (hβ ▸ hδ) hδN
    rw [map_conj_map_conj] at hgZ
    apply hgZ
    set ε := geo X α' α 2
    have hgα : g • α = α := (mem_stab X).mp hg
    have hk1 : (g * k) • α = g • δ := mul_smul g k α
    have hk2 : (g * k) • β = g • β := by rw [mul_smul, hkβ]
    have hαε : X.treeGraph.dist α ε = critDist X - 2 := by
      rw [SimpleGraph.dist_comm, dist_geo_right X (by rw [SimpleGraph.dist_comm]; omega),
        SimpleGraph.dist_comm, hd]
    have hgeo : geo X ((g * k) • α) ε 1 = (g * k) • β := by
      rw [hk1, hk2]
      refine geo_one_eq_of_adj X (n := critDist X - 1) ((adj_smul X g δ β).mpr hδ.symm)
        (by rw [hgc.2.1]; omega) ?_
      have := dist_triangle X (g • β) α ε
      rw [dist_smul_of_smul_eq X hgα, SimpleGraph.dist_comm (u := β) (v := α),
        dist_eq_one_of_adj X hαβ] at this
      omega
    have hεα' : X.treeGraph.dist ε α' = 2 := by
      rw [SimpleGraph.dist_comm, dist_geo X (by rw [SimpleGraph.dist_comm]; omega)]
    have hεM : IsMVtx X ε := isMVtx_geo_two X h hb0 (ms22_iii X h hb0 hC hcr)
    have h5 : Aαβ.map (MulAut.conj (g * k)).toMonoidHom ≤ Qv X α' :=
      ((hAd (g * k) ε (by rw [hk1]; exact hgc) hgeo).trans
        (commutator_xm_le_right X h hb0 hC (by rw [hk1]; exact hgc))).trans
        (ms22_i X h hC hεM hα' (by omega))
    exact (hZ.1.trans ((xm_le_centralizer X α').trans (Subgroup.centralizer_le h5))).trans
      (Subgroup.centralizer_le_normalizer _)
  refine ⟨?_, step4⟩
  obtain ⟨m, hm⟩ := ms21_v X h
  by_contra hne
  have hb6 : 6 ≤ critDist X := by omega
  obtain ⟨α', hcr, hβ⟩ := exists_isCritical_geo X h hb0 hα hαβ
  have hd : X.treeGraph.dist α α' = critDist X := hcr.2.1
  have hα' := hcr.isMVtx_right X h
  obtain ⟨δ, hδ, hδN⟩ := ms23_exists_adj_not_normal X h hb0 hC hcr
  obtain ⟨Z, hZ⟩ := hZall α α' hcr
  obtain ⟨g, hg, hgc, hgZ⟩ := ms23_step2 X h hb0 ha hC hG hcr hZ (N := Aαβ) (hβ ▸ hAT) hAG hδ hδN
  rw [hβ] at hδ
  apply hgZ
  set ε := geo X α' α 2
  have hgα : g • α = α := (mem_stab X).mp hg
  set a1 := g • β
  set a2 := g • δ
  have ha1 : X.treeGraph.Adj α a1 := by
    have := (adj_smul X g α β).mpr hαβ
    rwa [hgα] at this
  have ha12 : X.treeGraph.Adj a1 a2 := (adj_smul X g β δ).mpr hδ
  have hαε : X.treeGraph.dist α ε = critDist X - 2 := by
    rw [SimpleGraph.dist_comm, dist_geo_right X (by rw [SimpleGraph.dist_comm]; omega),
      SimpleGraph.dist_comm, hd]
  have ha2ε : X.treeGraph.dist a2 ε = critDist X := hgc.2.1
  have ha2α : X.treeGraph.dist a2 α = 2 := by
    have t1 := dist_triangle X a2 α ε
    have t2 := dist_triangle X a2 a1 α
    rw [dist_eq_one_of_adj X ha12.symm, dist_eq_one_of_adj X ha1.symm] at t2
    omega
  have hgeo1 : geo X a2 ε 1 = a1 := by
    refine geo_one_eq_of_adj X (n := critDist X - 1) ha12.symm (by omega) ?_
    have := dist_triangle X a1 α ε
    rw [dist_eq_one_of_adj X ha1.symm] at this
    omega
  have hgeo2 : geo X a2 ε 2 = α := by
    symm
    exact eq_geo_of_dist X ha2α (by omega)
  have h5v := ms22_v X h hb0 hC hV hgc
  rw [hgeo2] at h5v
  have ha2M : IsMVtx X a2 := hgc.1
  obtain ⟨Z', hZ'⟩ := hZall a2 ε hgc
  obtain ⟨t, ht, htc, -⟩ := ms23_step2 X h hb0 ha hC hG hgc hZ' (N := Qv X a1)
    (by rw [hgeo1]; exact Subgroup.le_normalizer)
    (not_stab_le_normalizer_qv X h ha2M ha12.symm) (by rw [hgeo1]; exact ha1.symm) h5v
  set φ := geo X α α' (critDist X - 4)
  have hαφ : X.treeGraph.dist α φ = critDist X - 4 := dist_geo X (by omega)
  have hεeq : ε = geo X α α' (critDist X - 2) := by
    have := geo_symm X (show critDist X - 2 ≤ X.treeGraph.dist α α' by omega)
    rw [hd, show critDist X - (critDist X - 2) = 2 by omega] at this
    exact this
  have hφε : X.treeGraph.dist φ ε = 2 := by
    rw [hεeq, dist_geo_geo X (by omega) (by omega)]
    omega
  have hφa2 : X.treeGraph.dist φ a2 = critDist X - 2 := by
    have t1 := dist_triangle X φ α a2
    have t2 := dist_triangle X ε φ a2
    rw [SimpleGraph.dist_comm (u := α) (v := a2), ha2α, SimpleGraph.dist_comm (u := φ) (v := α),
      hαφ] at t1
    rw [SimpleGraph.dist_comm (u := ε) (v := φ), hφε, SimpleGraph.dist_comm (u := ε) (v := a2),
      ha2ε] at t2
    omega
  have hgeoφ : geo X ε a2 2 = φ := by
    symm
    refine eq_geo_of_dist X (by rw [SimpleGraph.dist_comm]; exact hφε) ?_
    rw [SimpleGraph.dist_comm (u := ε) (v := φ), hφε, hφa2, SimpleGraph.dist_comm, ha2ε]
    omega
  rw [hgeoφ] at htc
  have htα : (t * g) • α = t • α := by rw [mul_smul, hgα]
  have htβ : (t * g) • β = t • a1 := mul_smul t g β
  have hta2 : t • a2 = a2 := (mem_stab X).mp ht
  have htαφ : X.treeGraph.dist (t • α) φ = critDist X := htc.2.1
  have htαa2 : X.treeGraph.dist (t • α) a2 = 2 := by
    rw [dist_smul_of_smul_eq X hta2, SimpleGraph.dist_comm, ha2α]
  have hgeoT1 : geo X ((t * g) • α) φ 1 = (t * g) • β := by
    rw [htα, htβ]
    refine geo_one_eq_of_adj X (n := critDist X - 1) ((adj_smul X t α a1).mpr ha1)
      (by omega) ?_
    have := dist_triangle X (t • a1) a2 φ
    rw [dist_smul_of_smul_eq X hta2, dist_eq_one_of_adj X ha12, SimpleGraph.dist_comm (u := a2),
      hφa2] at this
    omega
  have hgeoT2 : geo X ((t * g) • α) φ 2 = a2 := by
    rw [htα]
    symm
    refine eq_geo_of_dist X htαa2 ?_
    rw [htαa2, SimpleGraph.dist_comm (u := a2), hφa2, htαφ]
    omega
  have hφα' : X.treeGraph.dist φ α' = 4 := by
    rw [dist_geo_right X (by omega), hd]
    omega
  have hφM : IsMVtx X φ := htc.isMVtx_right X h
  have hAφ : Aαβ.map (MulAut.conj (t * g)).toMonoidHom ≤ Qv X α' :=
    ((hAd (t * g) φ (by rw [htα]; exact htc) hgeoT1).trans
      (commutator_xm_le_right X h hb0 hC (by rw [htα]; exact htc))).trans
      (ms22_i X h hC hφM hα' (by omega))
  have h4 : stab X a2 ≤ Subgroup.normalizer
      ((Aαβ.map (MulAut.conj (t * g)).toMonoidHom : Subgroup X.Universal) : Set X.Universal) := by
    have key := step4 ((t * g)⁻¹ • φ)
      (by have := (isCritical_smul X (t * g)⁻¹ _ _).mpr (htα ▸ htc); rwa [inv_smul_smul] at this)
      (by
        calc geo X α ((t * g)⁻¹ • φ) 1 = geo X ((t * g)⁻¹ • ((t * g) • α)) ((t * g)⁻¹ • φ) 1 := by
              rw [inv_smul_smul]
          _ = (t * g)⁻¹ • geo X ((t * g) • α) φ 1 := geo_smul X _ _ _ _
          _ = β := by rw [hgeoT1, inv_smul_smul])
    rw [← stab_le_normalizer_map_iff X (t * g)] at key
    have e : (t * g) • geo X α ((t * g)⁻¹ • φ) 2 = a2 := by
      rw [← geo_smul, smul_inv_smul, hgeoT2]
    rwa [e] at key
  have heq : Aαβ.map (MulAut.conj (t * g)).toMonoidHom = Aαβ.map (MulAut.conj g).toMonoidHom := by
    rw [← map_conj_eq_of_mem_normalizer (h4 (Subgroup.inv_mem _ ht)), map_conj_map_conj,
      ← mul_assoc, inv_mul_cancel, one_mul]
  rw [heq] at hAφ
  exact (hZ.1.trans ((xm_le_centralizer X α').trans (Subgroup.centralizer_le hAφ))).trans
    (Subgroup.centralizer_le_normalizer _)

end CFSG.Quasithin.MS93
