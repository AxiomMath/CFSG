module

public import CFSG.Quasithin.MS93.S38G2Off
public import CFSG.Quasithin.MS93.S32Crit

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.H13 CFSG.Quasithin.MS93
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem uq_normal (h : PUHyp M T L) : ((Uq M T L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Uq_le h.L_le)).2 (le_normalizer_Uq h.le_normalizer)

theorem uqzq_normal (h : PUHyp M T L) : ((Uq M T L ⊓ Zq M L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans (Uq_le h.L_le))).2
    (le_normalizer_inf (le_normalizer_Uq h.le_normalizer) (le_normalizer_Zq h.le_normalizer))

theorem l_normal (h : PUHyp M T L) : (L.subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer

omit [Finite G] in
theorem imM_map_conj (hTM : T ≤ M) {E : Subgroup G} (hEM : E ≤ M) (m : ↥M) :
    (imM hTM E).map (MulAut.conj ((puAmalgam hTM).ofA m)).toMonoidHom =
      imM hTM (E.map (MulAut.conj (m : G)).toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨m * e * m⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact ⟨e, Subgroup.mem_subgroupOf.mp he, rfl⟩
    · simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨e, he, hne⟩ := Subgroup.mem_subgroupOf.mp hn
    refine ⟨(puAmalgam hTM).ofA ⟨e, hEM he⟩, ⟨⟨e, hEM he⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩,
      ?_⟩
    have hn' : n = m * ⟨e, hEM he⟩ * m⁻¹ := by
      apply Subtype.ext
      rw [← hne]
      rfl
    simp only [hn', map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem exists_smul_crit (h : PUHyp M T L) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ γ') :
    ∃ (g : (puAmalgam h.le).Universal) (δ : Vtx (puAmalgam h.le)), γ = g • baseA _ ∧
      γ' = g • δ ∧ IsCritical (puAmalgam h.le) (baseA _) δ ∧
        geo (puAmalgam h.le) (baseA _) δ 1 = baseB _ := by
  have hγρ := adj_geo_one_of_isCritical _ h.critDist_pos hc
  obtain ⟨g, hg1, hg2⟩ := exists_smul_edge_of_isMVtx _ (PU.isMVtx_baseA _) (adj_baseA_baseB _)
    hc.1 hγρ
  refine ⟨g, g⁻¹ • γ', hg1.symm, by rw [smul_inv_smul], ?_, ?_⟩
  · have := (isCritical_smul _ g⁻¹ γ γ').mpr hc
    rwa [← hg1, inv_smul_smul] at this
  · have := geo_smul _ g⁻¹ γ γ' 1
    rw [← hg1, inv_smul_smul, hg1, ← hg2, inv_smul_smul] at this
    exact this

omit [Finite G] in
theorem commutator_le_M {H K : Subgroup G} (hH : H ≤ M) (hK : K ≤ M) : ⁅H, K⁆ ≤ M :=
  (Subgroup.commutator_mono hH hK).trans (Subgroup.commutator_le_self M)

omit [Finite G] in
theorem map_conj_le_M {E : Subgroup G} (hEM : E ≤ M) (m : ↥M) :
    E.map (MulAut.conj (m : G)).toMonoidHom ≤ M := by
  rintro _ ⟨e, he, rfl⟩
  exact M.mul_mem (M.mul_mem m.2 (hEM he)) (M.inv_mem m.2)

theorem commutator_Z0q_le_Uq (h : PUHyp M T L) {E : Subgroup G} (hET : E ≤ T) :
    ⁅Z0q M T, E⁆ ≤ Uq M T L := by
  rw [S33.commutator_Z0q_eq h hET]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((hET.trans h.le).trans (le_normalizer_Uq h.le_normalizer))

theorem conj_mem_map_conj_iff {Γ : Type*} [Group Γ] {K : Subgroup Γ} {g x : Γ} :
    (MulAut.conj g).toMonoidHom x ∈ K.map (MulAut.conj g).toMonoidHom ↔ x ∈ K :=
  Subgroup.mem_map_iff_mem (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem map_conj_conj {Γ : Type*} [Group Γ] (K : Subgroup Γ) (g a : Γ) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * a * g⁻¹)).toMonoidHom =
      (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel_right]

namespace G2Rep

variable {h : PUHyp M T L} {f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ}
  {φ : ↥M →* ↥(quasithinG2 (ZMod 2))}

theorem crit_le (hR : G2Rep h f φ) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) δ) :
    (S32.critIdx h δ).1 ≤ (S32.critIdx h δ).2.1 ∧
      (S32.critIdx h δ).2.1 ≤ (S32.critIdx h δ).2.2 := by
  obtain ⟨m, hm, hg⟩ := S32.exists_stab_smul_geo h hc
  rw [← S32.critIdx_smul h hm δ]
  have hc' : IsCritical (puAmalgam h.le) (baseA _) (m • δ) := by
    have := (isCritical_smul _ m (baseA _) δ).2 hc
    rwa [(mem_stab _).mp hm] at this
  have hZT := S32.zm_le_imM_T h hc' hg
  set E := S32.pullM h (ZM (puAmalgam h.le) (m • δ)) with hE
  have hET : E ≤ T := S32.pullM_le_T h hZT
  have hEim : imM h.le E = ZM (puAmalgam h.le) (m • δ) :=
    S32.imM_pullM h (hZT.trans (imM_mono h.le h.le))
  have hEab : IsElemAbelian 2 E :=
    S32.isElemAbelian_pullM h (isElemAbelian_zm _ h.hyp20 h.critDist_pos
      (hc'.isMVtx_right _ h.hyp20))
  have hZα : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  simp only [S32.critIdx]
  rw [← hEim, hZα, S32.relIndex_centralizer_imM h (hET.trans h.le) (Z0q_le M T),
    S32.relIndex_centralizer_imM h (Uq_le h.L_le) (hET.trans h.le),
    S32.relIndex_centralizer_imM h (Z0q_le M T) (hET.trans h.le)]
  refine ⟨?_, ?_⟩
  · have hinf : Subgroup.centralizer (Z0q M T : Set G) ⊓ E = pCoreOf 2 M ⊓ E := by
      rw [← h.centralizer_Z0q, inf_comm T (Subgroup.centralizer _), inf_assoc,
        inf_eq_right.2 hET]
    have hQ : (Subgroup.centralizer (Z0q M T : Set G)).relIndex E =
        (pCoreOf 2 M).relIndex E := by
      rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right]
    rw [hQ]
    exact hR.relIndex_le hET hEab
  · exact Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) Subgroup.FiniteIndex.index_ne_zero

theorem crit_eq (hR : G2Rep h f φ) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) δ) :
    (S32.critIdx h δ).1 = (S32.critIdx h δ).2.1 ∧
      (S32.critIdx h δ).2.1 = (S32.critIdx h δ).2.2 := by
  obtain ⟨h1, h2⟩ := hR.crit_le hc
  have hδ := hc.isMVtx_right _ h.hyp20
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  have hc' : IsCritical (puAmalgam h.le) (baseA _) (g⁻¹ • baseA (puAmalgam h.le)) := by
    have h3 := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
    have := (isCritical_smul _ g⁻¹ (g • baseA _) (baseA _)).2 h3
    rwa [inv_smul_smul] at this
  obtain ⟨h4, h5⟩ := hR.crit_le hc'
  have hrev : (S32.critIdx h (g • baseA (puAmalgam h.le))).2.2 ≤
      (S32.critIdx h (g • baseA (puAmalgam h.le))).1 := by
    have e1 : (S32.critIdx h (g⁻¹ • baseA (puAmalgam h.le))).1 =
        (S32.critIdx h (g • baseA (puAmalgam h.le))).2.2 := by
      simp only [S32.critIdx, zm_smul]
      rw [← S32.relIndex_centralizer_map_conj g, map_conj_map_conj_inv]
    have e2 : (S32.critIdx h (g⁻¹ • baseA (puAmalgam h.le))).2.2 =
        (S32.critIdx h (g • baseA (puAmalgam h.le))).1 := by
      simp only [S32.critIdx, zm_smul]
      rw [← S32.relIndex_centralizer_map_conj g, map_conj_map_conj_inv]
    rw [← e1, ← e2]
    exact h4.trans h5
  exact ⟨le_antisymm h1 (h2.trans hrev), le_antisymm h2 (hrev.trans h1)⟩

theorem exists_off (hR : G2Rep h f φ) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) δ)
    (hg : geo (puAmalgam h.le) (baseA _) δ 1 = baseB _) :
    ∃ E : Subgroup G, E ≤ T ∧ imM h.le E = ZM (puAmalgam h.le) δ ∧ IsElemAbelian 2 E ∧
      IsOffG2 (imB φ E) := by
  have hZT := S32.zm_le_imM_T h hc hg
  set E := S32.pullM h (ZM (puAmalgam h.le) δ) with hE
  have hET : E ≤ T := S32.pullM_le_T h hZT
  have hEim : imM h.le E = ZM (puAmalgam h.le) δ := S32.imM_pullM h (hZT.trans (imM_mono h.le h.le))
  have hEab : IsElemAbelian 2 E :=
    S32.isElemAbelian_pullM h (isElemAbelian_zm _ h.hyp20 h.critDist_pos
      (hc.isMVtx_right _ h.hyp20))
  refine ⟨E, hET, hEim, hEab, hR.isOffG2_of_relIndex_eq hET hEab ?_ ?_⟩
  · intro hle
    apply (ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc).2.2
    rw [← hEim, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
    exact imM_mono h.le hle
  · have h1 := (hR.crit_eq hc).1
    have hZα : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
    simp only [S32.critIdx] at h1
    rw [← hEim, hZα, S32.relIndex_centralizer_imM h (hET.trans h.le) (Z0q_le M T),
      S32.relIndex_centralizer_imM h (Uq_le h.L_le) (hET.trans h.le)] at h1
    have hinf : Subgroup.centralizer (Z0q M T : Set G) ⊓ E = pCoreOf 2 M ⊓ E := by
      rw [← h.centralizer_Z0q, inf_comm T (Subgroup.centralizer _), inf_assoc,
        inf_eq_right.2 hET]
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right] at h1
    exact h1

theorem offCent_base (hR : G2Rep h f φ) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) δ)
    (hg : geo (puAmalgam h.le) (baseA _) δ 1 = baseB _) :
    ∀ y ∈ Qv (puAmalgam h.le) (geo (puAmalgam h.le) (baseA _) δ 1),
      (∀ z ∈ ZM (puAmalgam h.le) δ, ⁅y, z⁆ ∈ Qv (puAmalgam h.le) (baseA _)) →
      y ∈ ZM (puAmalgam h.le) δ ⊔ Qv (puAmalgam h.le) (baseA (puAmalgam h.le)) := by
  obtain ⟨E, hET, hEim, -, hoff⟩ := hR.exists_off hc hg
  have hQ := puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  intro y hy hyz
  rw [hg, puAmalgam.qv_baseB] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have key : (t : G) ∈ E ⊔ pCoreOf 2 M := by
    refine hR.mem_sup_of_commute hET hoff (Subgroup.mem_subgroupOf.mp ht) fun e he => ?_
    have hz : (puAmalgam h.le).ofA ⟨e, h.le (hET he)⟩ ∈ ZM (puAmalgam h.le) δ := by
      rw [← hEim]
      exact (S33.ofA_mem_imM_iff h.le _).mpr he
    have h1 := hyz _ hz
    rw [hQ, ← map_commutatorElement, S33.ofA_mem_imM_iff] at h1
    exact h1
  rw [← hEim, hQ, ← S33.imM_sup h.le (hET.trans h.le) (pCoreOf_le' M)]
  exact (S33.ofA_mem_imM_iff h.le t).mpr key

theorem offCent (hR : G2Rep h f φ) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ γ') :
    ∀ y ∈ Qv (puAmalgam h.le) (geo (puAmalgam h.le) γ γ' 1),
      (∀ z ∈ ZM (puAmalgam h.le) γ', ⁅y, z⁆ ∈ Qv (puAmalgam h.le) γ) →
        y ∈ ZM (puAmalgam h.le) γ' ⊔ Qv (puAmalgam h.le) γ := by
  obtain ⟨g, δ, rfl, rfl, hcδ, hg⟩ := exists_smul_crit h hc
  have hb := hR.offCent_base hcδ hg
  intro y hy hyz
  rw [geo_smul, qv_smul] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  rw [zm_smul, qv_smul, ← Subgroup.map_sup]
  refine ⟨y₀, hb y₀ hy₀ fun z hz => ?_, rfl⟩
  have h1 := hyz ((MulAut.conj g).toMonoidHom z) (by rw [zm_smul]; exact ⟨z, hz, rfl⟩)
  rw [qv_smul, ← map_commutatorElement] at h1
  exact conj_mem_map_conj_iff.mp h1

omit [Finite G] in
theorem commutator_zm_base (hTM : T ≤ M) {δ : Vtx (puAmalgam hTM)} {E : Subgroup G}
    (hEM : E ≤ M) (hEim : imM hTM E = ZM (puAmalgam hTM) δ) :
    ⁅ZM (puAmalgam hTM) (baseA _), ZM (puAmalgam hTM) δ⁆ = imM hTM ⁅Z0q M T, E⁆ := by
  rw [← hEim, puAmalgam.zm_baseA hTM, S33.imM_commutator hTM (Z0q_le M T) hEM]

theorem offFix_base (hR : G2Rep h f φ) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) δ)
    (hg : geo (puAmalgam h.le) (baseA _) δ 1 = baseB _) :
    ∀ y ∈ Qv (puAmalgam h.le) (geo (puAmalgam h.le) (baseA _) δ 1),
      (∀ r ∈ ⁅ZM (puAmalgam h.le) (baseA _), ZM (puAmalgam h.le) δ⁆,
        ⁅r, y⁆ ∈ puTrans h.le (Uq M T L ⊓ Zq M L) (baseA _)) →
        y ∈ ZM (puAmalgam h.le) δ ⊔ Qv (puAmalgam h.le) (baseA (puAmalgam h.le)) := by
  obtain ⟨E, hET, hEim, -, hoff⟩ := hR.exists_off hc hg
  have hQ := puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hRim := commutator_zm_base h.le (hET.trans h.le) hEim
  intro y hy hyf
  rw [hg, puAmalgam.qv_baseB] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have key : (t : G) ∈ E ⊔ pCoreOf 2 M := by
    refine hR.mem_sup_of_fix hET hoff (Subgroup.mem_subgroupOf.mp ht) fun r hr => ?_
    have hrM : r ∈ M := commutator_le_M (Z0q_le M T) (hET.trans h.le) hr
    have h1 := hyf ((puAmalgam h.le).ofA ⟨r, hrM⟩) (by
      rw [hRim]
      exact (S33.ofA_mem_imM_iff h.le _).mpr hr)
    rw [puTrans_baseA h.le (uqzq_normal h), ← map_commutatorElement, S33.ofA_mem_imM_iff] at h1
    exact h1.2
  rw [← hEim, hQ, ← S33.imM_sup h.le (hET.trans h.le) (pCoreOf_le' M)]
  exact (S33.ofA_mem_imM_iff h.le t).mpr key

theorem offFix (hR : G2Rep h f φ) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ γ') :
    ∀ y ∈ Qv (puAmalgam h.le) (geo (puAmalgam h.le) γ γ' 1),
      (∀ r ∈ ⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) γ'⁆,
        ⁅r, y⁆ ∈ puTrans h.le (Uq M T L ⊓ Zq M L) γ) →
        y ∈ ZM (puAmalgam h.le) γ' ⊔ Qv (puAmalgam h.le) γ := by
  obtain ⟨g, δ, rfl, rfl, hcδ, hg⟩ := exists_smul_crit h hc
  have hb := hR.offFix_base hcδ hg
  intro y hy hyf
  rw [geo_smul, qv_smul] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  rw [zm_smul, qv_smul, ← Subgroup.map_sup]
  refine ⟨y₀, hb y₀ hy₀ fun r hr => ?_, rfl⟩
  have h1 := hyf ((MulAut.conj g).toMonoidHom r) (by
    rw [zm_smul, zm_smul, ← Subgroup.map_commutator]
    exact ⟨r, hr, rfl⟩)
  rw [puTrans_smul h.le (uqzq_normal h), ← map_commutatorElement] at h1
  exact conj_mem_map_conj_iff.mp h1

theorem rLe (hR : G2Rep h f φ) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ γ') :
    ⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) γ'⁆ ≤ puTrans h.le (Uq M T L) γ := by
  obtain ⟨g, δ, rfl, rfl, hcδ, hg⟩ := exists_smul_crit h hc
  obtain ⟨E, hET, hEim, -, -⟩ := hR.exists_off hcδ hg
  rw [zm_smul, zm_smul, ← Subgroup.map_commutator, puTrans_smul h.le (uq_normal h),
    commutator_zm_base h.le (hET.trans h.le) hEim, puTrans_baseA h.le (uq_normal h)]
  exact Subgroup.map_mono (imM_mono h.le (commutator_Z0q_le_Uq h hET))

theorem wLeR (h : PUHyp M T L)
    (hW : ∀ α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) (baseA _) α' →
      imM h.le (Uq M T L ⊓ Zq M L) ≤
        ⁅ZM (puAmalgam h.le) (baseA (puAmalgam h.le)), ZM (puAmalgam h.le) α'⁆)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) γ γ') :
    puTrans h.le (Uq M T L ⊓ Zq M L) γ ≤ ⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) γ'⁆ := by
  obtain ⟨g, δ, rfl, rfl, hcδ, -⟩ := exists_smul_crit h hc
  rw [puTrans_smul h.le (uqzq_normal h), zm_smul, zm_smul, ← Subgroup.map_commutator,
    puTrans_baseA h.le (uqzq_normal h)]
  exact Subgroup.map_mono (hW δ hcδ)

theorem rEq_base (hR : G2Rep h f φ)
    (hW : ∀ α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) (baseA _) α' →
      imM h.le (Uq M T L ⊓ Zq M L) ≤
        ⁅ZM (puAmalgam h.le) (baseA (puAmalgam h.le)), ZM (puAmalgam h.le) α'⁆)
    {δ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) (baseA _) δ)
    (hg : geo (puAmalgam h.le) (baseA _) δ 1 = baseB _) :
    ∀ u ∈ puTrans h.le (Uq M T L) (baseA _),
      (∀ z ∈ ZM (puAmalgam h.le) δ, ⁅u, z⁆ ∈ puTrans h.le (Uq M T L ⊓ Zq M L) (baseA _)) →
        u ∈ ⁅ZM (puAmalgam h.le) (baseA (puAmalgam h.le)), ZM (puAmalgam h.le) δ⁆ := by
  obtain ⟨E, hET, hEim, -, hoff⟩ := hR.exists_off hc hg
  have hRim := commutator_zm_base h.le (hET.trans h.le) hEim
  have hWR : Uq M T L ⊓ Zq M L ≤ ⁅Z0q M T, E⁆ := by
    have h1 := hW δ hc
    rwa [hRim, imM_le_imM_iff h.le (inf_le_left.trans (Uq_le h.L_le))] at h1
  intro u hu huf
  rw [puTrans_baseA h.le (uq_normal h)] at hu
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  rw [hRim]
  refine (S33.ofA_mem_imM_iff h.le u₀).mpr (hR.mem_commutator_of_fix hoff hWR
    (Subgroup.mem_subgroupOf.mp hu₀) fun e he => ?_)
  have hz : (puAmalgam h.le).ofA ⟨e, h.le (hET he)⟩ ∈ ZM (puAmalgam h.le) δ := by
    rw [← hEim]
    exact (S33.ofA_mem_imM_iff h.le _).mpr he
  have h1 := huf _ hz
  rw [puTrans_baseA h.le (uqzq_normal h), ← map_commutatorElement, S33.ofA_mem_imM_iff] at h1
  exact h1.2

theorem rEq (hR : G2Rep h f φ)
    (hW : ∀ α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) (baseA _) α' →
      imM h.le (Uq M T L ⊓ Zq M L) ≤
        ⁅ZM (puAmalgam h.le) (baseA (puAmalgam h.le)), ZM (puAmalgam h.le) α'⁆)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) γ γ') :
    ∀ u ∈ puTrans h.le (Uq M T L) γ,
      (∀ z ∈ ZM (puAmalgam h.le) γ', ⁅u, z⁆ ∈ puTrans h.le (Uq M T L ⊓ Zq M L) γ) →
        u ∈ ⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) γ'⁆ := by
  obtain ⟨g, δ, rfl, rfl, hcδ, hg⟩ := exists_smul_crit h hc
  have hb := hR.rEq_base hW hcδ hg
  intro u hu huf
  rw [puTrans_smul h.le (uq_normal h)] at hu
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  rw [zm_smul, zm_smul, ← Subgroup.map_commutator]
  refine ⟨u₀, hb u₀ hu₀ fun z hz => ?_, rfl⟩
  have h1 := huf ((MulAut.conj g).toMonoidHom z) (by rw [zm_smul]; exact ⟨z, hz, rfl⟩)
  rw [puTrans_smul h.le (uqzq_normal h), ← map_commutatorElement] at h1
  exact conj_mem_map_conj_iff.mp h1

theorem rCard (hR : G2Rep h f φ) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ γ') :
    2 < Nat.card ↥⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) γ'⁆ := by
  obtain ⟨g, δ, rfl, rfl, hcδ, hg⟩ := exists_smul_crit h hc
  obtain ⟨E, hET, hEim, -, hoff⟩ := hR.exists_off hcδ hg
  rw [zm_smul, zm_smul, ← Subgroup.map_commutator,
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
    commutator_zm_base h.le (hET.trans h.le) hEim,
    S33.card_imM h.le (commutator_le_M (Z0q_le M T) (hET.trans h.le))]
  have := hR.card_commutator hoff
  omega

theorem offIdx (hR : G2Rep h f φ) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ γ') :
    (Qv (puAmalgam h.le) γ).relIndex (ZM (puAmalgam h.le) γ') ≤ 8 := by
  obtain ⟨g, δ, rfl, rfl, hcδ, hg⟩ := exists_smul_crit h hc
  obtain ⟨E, hET, hEim, -, hoff⟩ := hR.exists_off hcδ hg
  rw [qv_smul, zm_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, ← hEim,
    S33.relIndex_imM h.le (hET.trans h.le), hR.relIndex_eq_eight hET hoff]

theorem twoGen_base
    (hR : G2Rep h f φ) {δ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) (baseA _) δ)
    (hg : geo (puAmalgam h.le) (baseA _) δ 1 = baseB _) :
    ∃ g₁ ∈ stab (puAmalgam h.le) (baseA (puAmalgam h.le)),
      ∃ g₂ ∈ stab (puAmalgam h.le) (baseA (puAmalgam h.le)),
      puTrans h.le L (baseA _) ≤ (ZM (puAmalgam h.le) δ).map (MulAut.conj g₁).toMonoidHom ⊔
        (ZM (puAmalgam h.le) δ).map (MulAut.conj g₂).toMonoidHom ⊔
          Qv (puAmalgam h.le) (baseA _) := by
  obtain ⟨E, hET, hEim, -, hoff⟩ := hR.exists_off hc hg
  have hEM : E ≤ M := hET.trans h.le
  obtain ⟨l₁, hl₁, l₂, hl₂, hL⟩ := hR.exists_two_gen hoff
  have hstab : ∀ (l : G) (hl : l ∈ L),
      (puAmalgam h.le).ofA ⟨l, h.L_le hl⟩ ∈ stab (puAmalgam h.le) (baseA (puAmalgam h.le)) := by
    intro l hl
    rw [puAmalgam.stab_baseA]
    exact ⟨⟨l, h.L_le hl⟩, Subgroup.mem_subgroupOf.mpr (h.L_le hl), rfl⟩
  refine ⟨_, hstab l₁ hl₁, _, hstab l₂ hl₂, ?_⟩
  rw [puTrans_baseA h.le (l_normal h), ← hEim, imM_map_conj h.le hEM, imM_map_conj h.le hEM,
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
    ← S33.imM_sup h.le (map_conj_le_M hEM ⟨l₁, h.L_le hl₁⟩) (map_conj_le_M hEM ⟨l₂, h.L_le hl₂⟩),
    ← S33.imM_sup h.le (sup_le (map_conj_le_M hEM ⟨l₁, h.L_le hl₁⟩)
      (map_conj_le_M hEM ⟨l₂, h.L_le hl₂⟩)) (pCoreOf_le' M)]
  exact imM_mono h.le hL

theorem twoGen
    (hR : G2Rep h f φ) {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) γ γ') :
    ∃ g₁ ∈ stab (puAmalgam h.le) γ, ∃ g₂ ∈ stab (puAmalgam h.le) γ, puTrans h.le L γ ≤
      (ZM (puAmalgam h.le) γ').map (MulAut.conj g₁).toMonoidHom ⊔
        (ZM (puAmalgam h.le) γ').map (MulAut.conj g₂).toMonoidHom ⊔
        Qv (puAmalgam h.le) γ := by
  obtain ⟨g, δ, rfl, rfl, hcδ, hg⟩ := exists_smul_crit h hc
  obtain ⟨g₁, hg₁, g₂, hg₂, hL⟩ := hR.twoGen_base hcδ hg
  refine ⟨g * g₁ * g⁻¹, ?_, g * g₂ * g⁻¹, ?_, ?_⟩
  · rw [stab_smul]
    exact conj_mem_map_conj hg₁
  · rw [stab_smul]
    exact conj_mem_map_conj hg₂
  · rw [puTrans_smul h.le (l_normal h), zm_smul, qv_smul, map_conj_conj, map_conj_conj,
      ← Subgroup.map_sup, ← Subgroup.map_sup]
    exact Subgroup.map_mono hL

end G2Rep

end CFSG.Quasithin.MS93.S38G
