module

public import CFSG.Quasithin.MS93.S33SpS5
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S33Stmt

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem pre_le_of_le_imM (h : PUHyp M T L) {S : Subgroup (puAmalgam h.le).Universal}
    {K : Subgroup G} (hS : S ≤ imM h.le K) : pre h.le S ≤ K := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := (mem_pre_iff' h.le).1 hx
  exact (ofA_mem_imM_iff h.le m).1 (hS hm)

theorem imM_closure_pair (h : PUHyp M T L) (m₁ m₂ : ↥M) :
    imM h.le (Subgroup.closure ({(m₁ : G), (m₂ : G)} : Set G)) =
      Subgroup.closure ({(puAmalgam h.le).ofA m₁, (puAmalgam h.le).ofA m₂} :
        Set (puAmalgam h.le).Universal) := by
  have e1 : Subgroup.closure ({(m₁ : G), (m₂ : G)} : Set G) =
      (Subgroup.closure ({m₁, m₂} : Set ↥M)).map M.subtype := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, Set.image_singleton]
  rw [e1, imM_map_subtype, MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq, Set.image_singleton]

theorem zm_le_imM_T (h : PUHyp M T L) {μ : Vtx (puAmalgam h.le)}
    (hμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hgeo : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _) :
    ZM (puAmalgam h.le) μ ≤ imM h.le T := by
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hμ
  have := zm_le_qv_geo_one _ h.hyp20 h.critDist_pos hc'
  rwa [hgeo, puAmalgam.qv_baseB] at this

theorem imM_commutator_pre (h : PUHyp M T L) {μ : Vtx (puAmalgam h.le)}
    (hμ : IsCritical (puAmalgam h.le) μ (baseA _)) (hET : pre h.le (ZM _ μ) ≤ T) :
    imM h.le ⁅Uq M T L, pre h.le (ZM _ μ)⁆ = critR (puAmalgam h.le) μ (baseA _) := by
  obtain ⟨-, -, -, -, hEim⟩ := pre_zm_props h hμ
  have hZ : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  rw [← commutator_Z0q_eq h hET, Subgroup.commutator_comm,
    imM_commutator h.le (pre_le h.le _) (Z0q_le M T), hEim, ← hZ, critR]

theorem conj_data (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {Y : Subgroup (puAmalgam h.le).Universal} (hyp : S33Hyp h α' Y)
    {g : (puAmalgam h.le).Universal} (hgα : g • baseA (puAmalgam h.le) = α')
    (hgβ : g • baseB (puAmalgam h.le) = geo _ α' (baseA _) 1)
    (hμ : IsCritical (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _))
    (hgeo : geo (puAmalgam h.le) (baseA _) (g⁻¹ • baseA _) 1 = baseB _) :
    pre h.le (ZM _ (g⁻¹ • baseA _)) ≤ T ∧
      pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ T ∧
      pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤
        Subgroup.centralizer ((⁅Uq M T L, pre h.le (ZM _ (g⁻¹ • baseA _))⁆ : Subgroup G) :
          Set G) ∧
      ¬ ⁅Uq M T L, pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom)⁆ ≤
        ⁅Uq M T L, pre h.le (ZM _ (g⁻¹ • baseA _))⁆ ∧
      (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) =
        (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ (g⁻¹ • baseA _)) ∧
      (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') =
        (Qv _ (g⁻¹ • baseA (puAmalgam h.le))).relIndex (ZM (puAmalgam h.le) (baseA _)) := by
  obtain ⟨hc, hY, hYR, hn⟩ := hyp
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hgμ : g • (g⁻¹ • baseA (puAmalgam h.le)) = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hYY' : Y = (Y.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    conv_lhs => rw [← Subgroup.map_id Y]
    congr 1
    ext x
    simp
  have hR : critR (puAmalgam h.le) (baseA _) α' =
      (critR (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _)).map (MulAut.conj g).toMonoidHom := by
    rw [critR, critR, Subgroup.map_commutator, ← zm_smul, ← zm_smul, hgμ, hgα]
  have hET : pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤ T :=
    pre_le_of_le_imM h (zm_le_imM_T h hμ hgeo)
  have hY'T : Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ imM h.le T := by
    intro y hy
    have hy' : (MulAut.conj g).toMonoidHom y ∈ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) := by
      rw [hYY'] at hY
      exact hY ⟨y, hy, rfl⟩
    rw [← hgβ, qv_smul, puAmalgam.qv_baseB] at hy'
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).1 hy'
  have hYqT : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ T := pre_le_of_le_imM h hY'T
  have hY'im : imM h.le (pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom)) =
      Y.map (MulAut.conj g⁻¹).toMonoidHom :=
    imM_pre h.le (hY'T.trans (imM_mono h.le h.le))
  have hcomm := imM_commutator_pre h hμ hET
  refine ⟨hET, hYqT, ?_, ?_, ?_, ?_⟩
  ·
    refine pre_le_centralizer h.le ((commutator_le_left_of_le_normalizer
      ((pre_le h.le _).trans (le_normalizer_Uq h.le_normalizer))).trans
        ((Uq_le_Z0q h.L_le).trans (Z0q_le M T))) ?_
    rw [hcomm]
    intro y hy
    have hy' : (MulAut.conj g).toMonoidHom y ∈
        Subgroup.centralizer (critR (puAmalgam h.le) (baseA _) α' : Set _) := by
      rw [hYY'] at hYR
      exact hYR ⟨y, hy, rfl⟩
    rw [hR, PU.centralizer_map_mulEquiv] at hy'
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).1 hy'
  ·
    intro hle
    apply hn
    refine le_sup_of_le_left ?_
    have h1 : ⁅ZM (puAmalgam h.le) (baseA _), Y.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤
        critR (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _) := by
      have hZ : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
      rw [hZ, ← hY'im, ← imM_commutator h.le (Z0q_le M T) (pre_le h.le _),
        commutator_Z0q_eq h hYqT, ← hcomm]
      exact imM_mono h.le hle
    have h2 : ⁅ZM (puAmalgam h.le) α', Y⁆ =
        ⁅ZM (puAmalgam h.le) (baseA _), Y.map (MulAut.conj g⁻¹).toMonoidHom⁆.map
          (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_commutator, ← hYY', ← zm_smul, hgα]
    rw [h2]
    refine (Subgroup.map_mono h1).trans ?_
    rw [← hR]
    exact Subgroup.commutator_mono (zm_le_xm _ h20 hb (PU.isMVtx_baseA _))
      (zm_le_xm _ h20 hb (hc.isMVtx_right _ h20))
  · have e1 : Qv (puAmalgam h.le) α' =
        (Qv (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← hgα, qv_smul]
    have e2 : ZM (puAmalgam h.le) (baseA _) =
        (ZM (puAmalgam h.le) (g⁻¹ • baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← zm_smul, hgμ]
    rw [e1, e2, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  · have e3 : Qv (puAmalgam h.le) (baseA _) =
        (Qv (puAmalgam h.le) (g⁻¹ • baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← qv_smul, hgμ]
    have e4 : ZM (puAmalgam h.le) α' =
        (ZM (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← hgα, zm_smul]
    rw [e4, e3, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem weak_of_pre (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {g : (puAmalgam h.le).Universal} (hgα : g • baseA (puAmalgam h.le) = α')
    (hgβ : g • baseB (puAmalgam h.le) = geo _ α' (baseA _) 1)
    (hμ : IsCritical (puAmalgam h.le) (g⁻¹ • baseA _) (baseA _)) {t₁ t₂ : G} (ht₁ : t₁ ∈ T)
    (ht₂ : t₂ ∈ T) (hi₁ : (Subgroup.centralizer ({t₁} : Set G)).relIndex (Z0q M T) = 2)
    (hi₂ : (Subgroup.centralizer ({t₂} : Set G)).relIndex (Z0q M T) = 2)
    (h12 : t₁ * t₂⁻¹ ∉ pCoreOf 2 M)
    (hsup : pre h.le (ZM _ (g⁻¹ • baseA _)) ⊔ pCoreOf 2 M =
      Subgroup.closure ({t₁, t₂} : Set G) ⊔ pCoreOf 2 M) :
    ∃ t₁ ∈ Qv _ (geo _ α' (baseA _) 1), ∃ t₂ ∈ Qv _ (geo _ α' (baseA _) 1),
      (∀ t ∈ ({t₁, t₂} : Set (puAmalgam h.le).Universal),
        (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2) ∧
      t₁ * t₂⁻¹ ∉ Qv _ α' ∧
      ZM _ (baseA _) ⊔ Qv _ α' =
        Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' := by
  have hgμ : g • (g⁻¹ • baseA (puAmalgam h.le)) = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hM₁ : t₁ ∈ M := h.le ht₁
  have hM₂ : t₂ ∈ M := h.le ht₂
  have hQα : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hZ : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  obtain ⟨-, -, -, -, hEim⟩ := pre_zm_props h hμ
  have hmemQ : ∀ {t : G} (ht : t ∈ T), (MulAut.conj g).toMonoidHom
      ((puAmalgam h.le).ofA ⟨t, h.le ht⟩) ∈ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) := by
    intro t ht
    rw [← hgβ, qv_smul, puAmalgam.qv_baseB]
    exact ⟨_, (ofA_mem_imM_iff h.le _).2 ht, rfl⟩
  have hidx : ∀ {t : G} (ht : t ∈ T),
      (Subgroup.centralizer ({t} : Set G)).relIndex (Z0q M T) = 2 →
      (Subgroup.centralizer ({(MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨t, h.le ht⟩)} :
        Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2 := by
    intro t ht hi
    rw [centralizer_singleton_conj, ← hgα, zm_smul,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hZ,
      relIndex_centralizer_ofA h ⟨t, h.le ht⟩ (Z0q_le M T)]
    exact hi
  refine ⟨_, hmemQ ht₁, _, hmemQ ht₂, ?_, ?_, ?_⟩
  · rintro t (rfl | rfl)
    · exact hidx ht₁ hi₁
    · exact hidx ht₂ hi₂
  · intro hmem
    rw [← map_inv, ← map_mul, ← hgα, qv_smul,
      Subgroup.mem_map_iff_mem (MulAut.conj g).injective, hQα, ← map_inv, ← map_mul,
      ofA_mem_imM_iff] at hmem
    exact h12 hmem
  · have hcl : Subgroup.closure ({(MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨t₁, hM₁⟩),
        (MulAut.conj g).toMonoidHom ((puAmalgam h.le).ofA ⟨t₂, hM₂⟩)} :
          Set (puAmalgam h.le).Universal) =
        (Subgroup.closure ({(puAmalgam h.le).ofA ⟨t₁, hM₁⟩, (puAmalgam h.le).ofA ⟨t₂, hM₂⟩} :
          Set (puAmalgam h.le).Universal)).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_closure]
      congr 1
      simp [Set.image_insert_eq, Set.image_singleton]
    have hbase : ZM (puAmalgam h.le) (g⁻¹ • baseA _) ⊔ Qv (puAmalgam h.le) (baseA _) =
        Subgroup.closure ({(puAmalgam h.le).ofA ⟨t₁, hM₁⟩, (puAmalgam h.le).ofA ⟨t₂, hM₂⟩} :
          Set (puAmalgam h.le).Universal) ⊔ Qv (puAmalgam h.le) (baseA _) := by
      rw [← hEim, hQα, ← imM_sup h.le (pre_le h.le _) (pCoreOf_le' M), hsup,
        imM_sup h.le ((Subgroup.closure_le _).2 (by
          rintro _ (rfl | rfl)
          · exact hM₁
          · exact hM₂)) (pCoreOf_le' M), imM_closure_pair h ⟨t₁, hM₁⟩ ⟨t₂, hM₂⟩]
    have e5 : ZM (puAmalgam h.le) (baseA _) =
        (ZM (puAmalgam h.le) (g⁻¹ • baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← zm_smul, hgμ]
    have e6 : Qv (puAmalgam h.le) α' =
        (Qv (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom := by
      rw [← hgα, qv_smul]
    rw [hcl, e5, e6, ← Subgroup.map_sup, ← Subgroup.map_sup, hbase]

end CFSG.Quasithin.MS93.S33
