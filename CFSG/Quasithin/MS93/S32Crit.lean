module

public import CFSG.Quasithin.MS93.S32U

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] def NoStrongOffU (h : PUHyp M T L) : Prop :=
  ∀ A : Subgroup (MulAut (IntMod (Uq M T L) h.isElemAbelian_Uq)),
    A ≤ autI h.isElemAbelian_Uq M → IsElemAbelian2 A →
      Nat.card A * Nat.card (fixV A) ≤ Nat.card ↥(Uq M T L)

theorem relIndex_le_relIndex_Uq (h : PUHyp M T L) (hN : NoStrongOffU h) {E : Subgroup G}
    (hET : E ≤ T) (hE : IsElemAbelian 2 E) :
    (pCoreOf 2 M).relIndex E ≤ (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) := by
  set hU := h.isElemAbelian_Uq
  have hEN : E ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hET.trans (h.le.trans (le_normalizer_Uq h.le_normalizer))
  have h1 := hN (autI hU E) (autI_mono hU (hET.trans h.le)) (isElemAbelian2_autI hU hE hEN)
  rw [(isSecW_Uq h).card_autI_of_le_T h hET, card_fixV_autI hU hEN] at h1
  have hcard := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) (Uq M T L)
  rw [← hcard, inf_comm] at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem relIndex_centralizer_imM (h : PUHyp M T L) {K K' : Subgroup G} (hK : K ≤ M)
    (hK' : K' ≤ M) :
    (Subgroup.centralizer (imM h.le K' : Set (puAmalgam h.le).Universal)).relIndex
        (imM h.le K) = (Subgroup.centralizer (K' : Set G)).relIndex K := by
  rw [← Subgroup.inf_relIndex_right, inf_comm, ← imM_inf_centralizer h.le K hK',
    imM_relIndex h.le _ hK, inf_comm, Subgroup.inf_relIndex_right]

@[expose] def pullM (h : PUHyp M T L) (K : Subgroup (puAmalgam h.le).Universal) : Subgroup G :=
  (K.comap (puAmalgam h.le).ofA).map M.subtype

theorem pullM_le (h : PUHyp M T L) (K : Subgroup (puAmalgam h.le).Universal) :
    pullM h K ≤ M :=
  Subgroup.map_subtype_le _

theorem imM_pullM (h : PUHyp M T L) {K : Subgroup (puAmalgam h.le).Universal}
    (hK : K ≤ imM h.le M) : imM h.le (pullM h K) = K := by
  have hrange : K ≤ (puAmalgam h.le).ofA.range := by
    refine hK.trans ?_
    rintro _ ⟨m, -, rfl⟩
    exact ⟨m, rfl⟩
  rw [pullM, imM_map_subtype, Subgroup.map_comap_eq, inf_eq_right.2 hrange]

theorem pullM_le_T (h : PUHyp M T L) {K : Subgroup (puAmalgam h.le).Universal}
    (hK : K ≤ imM h.le T) : pullM h K ≤ T := by
  have hKM : K ≤ imM h.le M := hK.trans (imM_mono h.le h.le)
  rw [← imM_le_imM_iff h.le (pullM_le h K), imM_pullM h hKM]
  exact hK

theorem isElemAbelian_pullM (h : PUHyp M T L) {K : Subgroup (puAmalgam h.le).Universal}
    (hK : IsElemAbelian 2 K) : IsElemAbelian 2 (pullM h K) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    have hc : (puAmalgam h.le).ofA a * (puAmalgam h.le).ofA b =
        (puAmalgam h.le).ofA b * (puAmalgam h.le).ofA a := by
      have := hK.1.1.1 ⟨_, ha⟩ ⟨_, hb⟩
      exact congrArg Subtype.val this
    rw [← map_mul, ← map_mul] at hc
    have := (puAmalgam h.le).ofA_injective hc
    apply Subtype.ext
    show (x : G) * y = y * x
    rw [← hax, ← hby]
    exact congrArg Subtype.val this
  · obtain ⟨a, ha, rfl⟩ := hx
    have h1 : (puAmalgam h.le).ofA (a ^ 2) = 1 := by rw [map_pow]; exact hK.2 _ ha
    have h2 : a ^ 2 = 1 := (puAmalgam h.le).ofA_injective (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2

theorem stab_le_normalizer_imM (h : PUHyp M T L) {N : Subgroup G}
    (hN : M ≤ Subgroup.normalizer (N : Set G)) :
    stab (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (imM h.le N : Set (puAmalgam h.le).Universal) := by
  rw [puAmalgam.stab_baseA]
  rintro _ ⟨m, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨m * n * m⁻¹, ?_, by simp⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hN m.2) n).1 hn
  · rintro ⟨n, hn, hnx⟩
    refine ⟨m⁻¹ * n * m, ?_, ?_⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hn ⊢
      have := (Subgroup.mem_normalizer_iff.1 (hN (M.inv_mem m.2)) n).1 hn
      simpa [mul_assoc] using this
    · rw [map_mul, map_mul, map_inv, hnx]
      group

theorem exists_stab_smul_geo (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) δ) :
    ∃ m ∈ stab (puAmalgam h.le) (baseA _), geo _ (baseA _) (m • δ) 1 = baseB _ := by
  have hd : 0 < (puAmalgam h.le).treeGraph.dist (baseA _) δ := by
    rw [hc.2.1]
    exact h.critDist_pos
  obtain ⟨m, hm, hmγ⟩ := exists_mem_stab_smul _ (adj_geo_one _ hd) (adj_baseA_baseB _)
  refine ⟨m, hm, ?_⟩
  have hmα : m • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).mp hm
  calc geo _ (baseA _) (m • δ) 1 = geo _ (m • baseA _) (m • δ) 1 := by rw [hmα]
    _ = m • geo _ (baseA _) δ 1 := geo_smul _ m (baseA _) δ 1
    _ = baseB _ := hmγ

theorem zm_le_imM_T (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) δ) (hg : geo _ (baseA _) δ 1 = baseB _) :
    ZM _ δ ≤ imM h.le T := by
  rw [← puAmalgam.qv_baseB h.le, ← hg]
  have hb := h.critDist_pos
  have hd : 1 ≤ (puAmalgam h.le).treeGraph.dist (baseA _) δ := by rw [hc.2.1]; omega
  apply zm_le_qv_of_dist_lt _ (hc.isMVtx_right _ h.hyp20)
  rw [SimpleGraph.dist_comm, dist_geo_right _ hd, hc.2.1]
  omega

@[expose] noncomputable def critIdx (h : PUHyp M T L) (δ : Vtx (puAmalgam h.le)) : ℕ × ℕ × ℕ :=
  ((Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set _)).relIndex (ZM _ δ),
    (Subgroup.centralizer (ZM _ δ : Set _)).relIndex (imM h.le (Uq M T L)),
    (Subgroup.centralizer (ZM _ δ : Set _)).relIndex (ZM _ (baseA (puAmalgam h.le))))

theorem relIndex_centralizer_map_conj {Γ : Type*} [Group Γ] (g : Γ) (A B : Subgroup Γ) :
    (Subgroup.centralizer (A.map (MulAut.conj g).toMonoidHom : Set Γ)).relIndex
        (B.map (MulAut.conj g).toMonoidHom) =
      (Subgroup.centralizer (A : Set Γ)).relIndex B := by
  rw [PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem critIdx_smul (h : PUHyp M T L) {m : (puAmalgam h.le).Universal}
    (hm : m ∈ stab (puAmalgam h.le) (baseA _)) (δ : Vtx (puAmalgam h.le)) :
    critIdx h (m • δ) = critIdx h δ := by
  have hZ : (ZM _ (baseA (puAmalgam h.le))).map (MulAut.conj m).toMonoidHom =
      ZM _ (baseA (puAmalgam h.le)) :=
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ _ hm)
  have hU : (imM h.le (Uq M T L)).map (MulAut.conj m).toMonoidHom = imM h.le (Uq M T L) :=
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_imM h (le_normalizer_Uq h.le_normalizer) hm)
  have key := relIndex_centralizer_map_conj m
  simp only [critIdx, zm_smul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set _)).relIndex
        ((ZM _ δ).map (MulAut.conj m).toMonoidHom) = _
    conv_lhs => rw [← hZ]
    exact key _ _
  · show (Subgroup.centralizer ((ZM _ δ).map (MulAut.conj m).toMonoidHom : Set _)).relIndex
        (imM h.le (Uq M T L)) = _
    conv_lhs => rw [← hU]
    exact key _ _
  · show (Subgroup.centralizer ((ZM _ δ).map (MulAut.conj m).toMonoidHom : Set _)).relIndex
        (ZM _ (baseA (puAmalgam h.le))) = _
    conv_lhs => rw [← hZ]
    exact key _ _

theorem crit_le (h : PUHyp M T L) (hN : NoStrongOffU h) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) δ) :
    (critIdx h δ).1 ≤ (critIdx h δ).2.1 ∧ (critIdx h δ).2.1 ≤ (critIdx h δ).2.2 := by
  obtain ⟨m, hm, hg⟩ := exists_stab_smul_geo h hc
  rw [← critIdx_smul h hm δ]
  have hc' : IsCritical _ (baseA _) (m • δ) := by
    have := (isCritical_smul _ m (baseA _) δ).2 hc
    rwa [(mem_stab _).mp hm] at this
  have hZT := zm_le_imM_T h hc' hg
  set E := pullM h (ZM _ (m • δ)) with hE
  have hET : E ≤ T := pullM_le_T h hZT
  have hEim : imM h.le E = ZM _ (m • δ) := imM_pullM h (hZT.trans (imM_mono h.le h.le))
  have hEab : IsElemAbelian 2 E :=
    isElemAbelian_pullM h (isElemAbelian_zm _ h.hyp20 h.critDist_pos (hc'.isMVtx_right _ h.hyp20))
  have hZα : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  simp only [critIdx]
  rw [← hEim, hZα, relIndex_centralizer_imM h (hET.trans h.le) (Z0q_le M T),
    relIndex_centralizer_imM h (Uq_le h.L_le) (hET.trans h.le),
    relIndex_centralizer_imM h (Z0q_le M T) (hET.trans h.le)]
  refine ⟨?_, ?_⟩
  · have hinf : Subgroup.centralizer (Z0q M T : Set G) ⊓ E = pCoreOf 2 M ⊓ E := by
      rw [← h.centralizer_Z0q, inf_comm T (Subgroup.centralizer _), inf_assoc,
        inf_eq_right.2 hET]
    have hQ : (Subgroup.centralizer (Z0q M T : Set G)).relIndex E = (pCoreOf 2 M).relIndex E := by
      rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right]
    rw [hQ]
    exact relIndex_le_relIndex_Uq h hN hET hEab
  · exact Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) Subgroup.FiniteIndex.index_ne_zero

theorem crit_eq (h : PUHyp M T L) (hN : NoStrongOffU h) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) δ) :
    (critIdx h δ).1 = (critIdx h δ).2.1 ∧ (critIdx h δ).2.1 = (critIdx h δ).2.2 := by
  obtain ⟨h1, h2⟩ := crit_le h hN hc
  have hδ := hc.isMVtx_right _ h.hyp20
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  have hc' : IsCritical _ (baseA _) (g⁻¹ • baseA (puAmalgam h.le)) := by
    have h3 := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
    have := (isCritical_smul _ g⁻¹ (g • baseA _) (baseA _)).2 h3
    rwa [inv_smul_smul] at this
  obtain ⟨h4, h5⟩ := crit_le h hN hc'
  have hrev : (critIdx h (g • baseA (puAmalgam h.le))).2.2 ≤
      (critIdx h (g • baseA (puAmalgam h.le))).1 := by
    have e1 : (critIdx h (g⁻¹ • baseA (puAmalgam h.le))).1 =
        (critIdx h (g • baseA (puAmalgam h.le))).2.2 := by
      simp only [critIdx, zm_smul]
      rw [← relIndex_centralizer_map_conj g, map_conj_map_conj_inv]
    have e2 : (critIdx h (g⁻¹ • baseA (puAmalgam h.le))).2.2 =
        (critIdx h (g • baseA (puAmalgam h.le))).1 := by
      simp only [critIdx, zm_smul]
      rw [← relIndex_centralizer_map_conj g, map_conj_map_conj_inv]
    rw [← e1, ← e2]
    exact h4.trans h5
  exact ⟨le_antisymm h1 (h2.trans hrev), le_antisymm h2 (hrev.trans h1)⟩

theorem sup_eq_of_relIndex_eq {Γ : Type*} [Group Γ] {U Z C : Subgroup Γ} [Finite Z]
    (hUZ : U ≤ Z) (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (he : C.relIndex U = C.relIndex Z) :
    U ⊔ (Z ⊓ C) = Z := by
  set U₁ := U.subgroupOf Z
  set K₁ := C.subgroupOf Z
  have hK₁ : K₁.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hZ _ g.2 _ n.2, mul_inv_cancel_right]
    rw [this]
    exact hn⟩
  have h1 : K₁.relIndex (U₁ ⊔ K₁) = K₁.relIndex ⊤ := by
    rw [Subgroup.relIndex_sup_right, Subgroup.relIndex_subgroupOf hUZ, he,
      ← Subgroup.relIndex_subgroupOf le_rfl, Subgroup.subgroupOf_self]
  have h2 := Subgroup.relIndex_mul_relIndex K₁ (U₁ ⊔ K₁) ⊤ le_sup_right le_top
  have hne : K₁.relIndex ⊤ ≠ 0 := Subgroup.FiniteIndex.index_ne_zero (H := K₁.subgroupOf ⊤)
  rw [h1] at h2
  have h3 : (U₁ ⊔ K₁).relIndex ⊤ = 1 := by
    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (h2.trans (mul_one _).symm)
    exact this
  have h4 : U₁ ⊔ K₁ = ⊤ := top_le_iff.mp (Subgroup.relIndex_eq_one.mp h3)
  have h5 := congrArg (Subgroup.map Z.subtype) h4
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, inf_eq_left.2 hUZ, inf_comm] at h5
  exact h5

theorem zm_eq_sup_of_crit (h : PUHyp M T L) (hN : NoStrongOffU h) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) δ) :
    imM h.le (Uq M T L) ⊔ (ZM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (ZM _ δ : Set _)) = ZM _ (baseA (puAmalgam h.le)) := by
  have hZα : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  have hUZ : imM h.le (Uq M T L) ≤ ZM _ (baseA (puAmalgam h.le)) := by
    rw [hZα]
    exact imM_mono h.le (Uq_le_Z0q h.L_le)
  have hfin : Finite ↥(ZM (puAmalgam h.le) (baseA _)) := by
    rw [hZα, imM]
    exact Finite.of_surjective _ (Subgroup.equivMapOfInjective _ _
      (puAmalgam h.le).ofA_injective).surjective
  refine sup_eq_of_relIndex_eq hUZ (fun x hx y hy => ?_) (crit_eq h hN hc).2
  have := (isElemAbelian_zm _ h.hyp20 h.critDist_pos (isMVtx_baseA _)).1.1.1 ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

end CFSG.Quasithin.MS93.S32
