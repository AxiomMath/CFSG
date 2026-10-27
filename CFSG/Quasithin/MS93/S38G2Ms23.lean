module

public import CFSG.Quasithin.MS93.S38G2Vtx
public import CFSG.Quasithin.MS93.S38G2Step

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.H13 CFSG.Quasithin.MS93
open scoped commutatorElement

theorem cRel_map_map_conj {Γ : Type*} [Group Γ] (A N : Subgroup Γ) (g : Γ) :
    cRel (A.map (MulAut.conj g).toMonoidHom) (N.map (MulAut.conj g).toMonoidHom) =
      (cRel A N).map (MulAut.conj g).toMonoidHom := by
  ext x
  obtain ⟨x₀, rfl⟩ : ∃ x₀, (MulAut.conj g).toMonoidHom x₀ = x :=
    ⟨g⁻¹ * x * g, by simp [mul_assoc]⟩
  rw [conj_mem_map_conj_iff, mem_cRel, mem_cRel,
    ← Subgroup.map_equiv_normalizer_eq N (MulAut.conj g), conj_mem_map_conj_iff]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨hn, fun a ha => ?_⟩
    have h1 := hc _ ⟨a, ha, rfl⟩
    rw [← map_commutatorElement] at h1
    exact conj_mem_map_conj_iff.mp h1
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_commutatorElement]
    exact conj_mem_map_conj_iff.mpr (hc a ha)

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] noncomputable def aSub (h : PUHyp M T L) (γ ρ : Vtx (puAmalgam h.le)) :
    Subgroup (puAmalgam h.le).Universal :=
  puTrans h.le (Uq M T L) γ ⊓
    cRel (Qv (puAmalgam h.le) ρ) (puTrans h.le (Uq M T L ⊓ Zq M L) γ)

theorem mem_aSub (h : PUHyp M T L) {γ ρ : Vtx (puAmalgam h.le)}
    {u : (puAmalgam h.le).Universal} :
    u ∈ aSub h γ ρ ↔ u ∈ puTrans h.le (Uq M T L) γ ∧
      ∀ t ∈ Qv (puAmalgam h.le) ρ, ⁅u, t⁆ ∈ puTrans h.le (Uq M T L ⊓ Zq M L) γ := by
  constructor
  · rintro ⟨hu, -, hut⟩
    exact ⟨hu, hut⟩
  · rintro ⟨hu, hut⟩
    exact ⟨hu, stab_le_normalizer_puTrans h.le (uqzq_normal h) γ (puTrans_le_stab h.le _ γ hu),
      hut⟩

theorem aSub_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (γ ρ : Vtx (puAmalgam h.le)) :
    aSub h (g • γ) (g • ρ) = (aSub h γ ρ).map (MulAut.conj g).toMonoidHom := by
  rw [aSub, aSub, puTrans_smul h.le (uq_normal h), puTrans_smul h.le (uqzq_normal h), qv_smul,
    cRel_map_map_conj, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

theorem wt_le_aSub (h : PUHyp M T L) {γ ρ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) :
    puTrans h.le (Uq M T L ⊓ Zq M L) γ ≤ aSub h γ ρ := by
  intro w hw
  have hWU : puTrans h.le (Uq M T L ⊓ Zq M L) γ ≤ puTrans h.le (Uq M T L) γ := by
    rw [wt_eq h hγ]
    exact inf_le_left
  refine (mem_aSub h).mpr ⟨hWU hw, fun t ht => ?_⟩
  have htN := (qv_le_stab_of_isMVtx _ h.hyp20 hγ hγρ).trans
    (stab_le_normalizer_puTrans h.le (uqzq_normal h) γ) ht
  have e : ⁅w, t⁆ = w * (t * w⁻¹ * t⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ hw ((Subgroup.mem_normalizer_iff.mp htN _).mp (Subgroup.inv_mem _ hw))

theorem qv_le_normalizer_aSub (h : PUHyp M T L) {γ ρ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) :
    Qv (puAmalgam h.le) ρ ≤ Subgroup.normalizer (aSub h γ ρ : Set (puAmalgam h.le).Universal) := by
  have hQ : Qv (puAmalgam h.le) ρ ≤ stab (puAmalgam h.le) γ :=
    qv_le_stab_of_isMVtx _ h.hyp20 hγ hγρ
  exact le_normalizer_inf' (hQ.trans (stab_le_normalizer_puTrans h.le (uq_normal h) γ))
    (le_normalizer_cRel Subgroup.le_normalizer
      (hQ.trans (stab_le_normalizer_puTrans h.le (uqzq_normal h) γ)))

namespace G2Rep

variable {h : PUHyp M T L} {f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ}
  {φ : ↥M →* ↥(quasithinG2 (ZMod 2))}

theorem zc23At (hR : G2Rep h f φ) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ γ') :
    Zc23At (puAmalgam h.le) γ γ' (XM (puAmalgam h.le) γ') := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hc' := ms22_iii _ h20 hb0 hC hc
  refine ⟨le_rfl, xm_not_le_qv_of_isCritical h20 hb0 hC hc, fun Y hY hYab => ?_⟩
  have hYle : Y ≤ ZM (puAmalgam h.le) γ ⊔ Qv (puAmalgam h.le) γ' := by
    intro y hy
    refine hR.offCent hc' y (hY hy) fun z hz => ?_
    have hcomm : y * z = z * y := by
      have := hYab.1.1.1 ⟨y, Subgroup.mem_sup_left hy⟩
        ⟨z, Subgroup.mem_sup_right (zm_le_xm _ h20 hb0 hc.1 hz)⟩
      exact congrArg Subtype.val this
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact Subgroup.one_mem _
  have hZn : ZM (puAmalgam h.le) γ ≤
      Subgroup.normalizer (XM (puAmalgam h.le) γ' : Set (puAmalgam h.le).Universal) :=
    (zm_le_stab_of_isCritical _ h20 hb0 hc').trans (stab_le_normalizer_xm _ γ')
  refine le_sup_of_le_left ?_
  calc ⁅Y, XM (puAmalgam h.le) γ'⁆
      ≤ ⁅ZM (puAmalgam h.le) γ ⊔ Qv (puAmalgam h.le) γ', XM (puAmalgam h.le) γ'⁆ :=
        Subgroup.commutator_mono hYle le_rfl
    _ = ⁅XM (puAmalgam h.le) γ', ZM (puAmalgam h.le) γ ⊔ Qv (puAmalgam h.le) γ'⁆ :=
        Subgroup.commutator_comm _ _
    _ = ⁅XM (puAmalgam h.le) γ', ZM (puAmalgam h.le) γ⁆ :=
        commutator_sup_eq_of_le_centralizer hZn (qv_le_centralizer_xm _ γ')
    _ = ⁅ZM (puAmalgam h.le) γ, XM (puAmalgam h.le) γ'⁆ := Subgroup.commutator_comm _ _
    _ ≤ ⁅XM (puAmalgam h.le) γ, XM (puAmalgam h.le) γ'⁆ :=
        Subgroup.commutator_mono (zm_le_xm _ h20 hb0 hc.1) le_rfl

theorem eq_or_eq_of_le_normalizer (hR : G2Rep h f φ) {A₀ : Subgroup G}
    (hWA : Uq M T L ⊓ Zq M L ≤ A₀) (hAU : A₀ ≤ Uq M T L)
    (hAn : L ≤ Subgroup.normalizer (A₀ : Set G)) :
    A₀ = Uq M T L ⊓ Zq M L ∨ A₀ = Uq M T L := by
  set A' : Subgroup ModQ := (A₀.comap (intModVal h.isElemAbelian_Uq)).map f with hA'
  have hinv : ∀ δ ∈ g2Derived (ZMod 2), ∀ q ∈ A', g2QAct (ZMod 2) δ q ∈ A' := by
    rintro δ hδ _ ⟨v, hv, rfl⟩
    obtain ⟨l, hl, rfl⟩ := hR.L_onto δ hδ
    refine ⟨convM h l v, ?_, hR.equiv l v⟩
    change (convM h l v).val ∈ A₀
    rw [convM_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (hAn hl) _).mp hv
  rcases modQ_irred A' hinv with hbot | htop
  · left
    refine le_antisymm (fun a ha => ⟨hAU ha, ?_⟩) hWA
    have h1 : f (IntMod.mk _ ⟨a, hAU ha⟩) ∈ A' := ⟨_, ha, rfl⟩
    rw [hbot, Subgroup.mem_bot, hR.ker] at h1
    exact h1
  · right
    refine le_antisymm hAU fun u hu => ?_
    have h1 : f (IntMod.mk _ ⟨u, hu⟩) ∈ A' := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨v, hv, hvu⟩ := h1
    have h2 : f (v⁻¹ * IntMod.mk _ ⟨u, hu⟩) = 1 := by
      rw [map_mul, map_inv, hvu, inv_mul_cancel]
    have h3 : (v⁻¹ * IntMod.mk h.isElemAbelian_Uq ⟨u, hu⟩).val ∈ A₀ :=
      hWA ⟨(v⁻¹ * IntMod.mk h.isElemAbelian_Uq ⟨u, hu⟩).val_mem, (hR.ker _).mp h2⟩
    have e : u = v.val * (v⁻¹ * IntMod.mk h.isElemAbelian_Uq ⟨u, hu⟩).val := by
      rw [IntMod.val_mul, IntMod.val_inv, mul_inv_cancel_left]
      rfl
    rw [e]
    exact A₀.mul_mem hv h3

theorem not_stab_le_normalizer_aSub_base (hR : G2Rep h f φ) :
    ¬ stab (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (aSub h (baseA _) (baseB _) : Set (puAmalgam h.le).Universal) := by
  intro hN
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hU : puTrans h.le (Uq M T L) (baseA _) = imM h.le (Uq M T L) :=
    puTrans_baseA h.le (uq_normal h)
  have hW : puTrans h.le (Uq M T L ⊓ Zq M L) (baseA _) = imM h.le (Uq M T L ⊓ Zq M L) :=
    puTrans_baseA h.le (uqzq_normal h)
  have hQ := puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hQβ : Qv (puAmalgam h.le) (baseB _) = imM h.le T := puAmalgam.qv_baseB h.le
  obtain ⟨x, hx, hxW⟩ : ∃ x ∈ aSub h (baseA _) (baseB _),
      x ∉ puTrans h.le (Uq M T L ⊓ Zq M L) (baseA _) := by
    have hβ := PU.not_isMVtx_baseB (puAmalgam h.le)
    have : Finite ↥(Qv (puAmalgam h.le) (baseB _)) := finite_qv _ h20 hβ
    have hWU : puTrans h.le (Uq M T L ⊓ Zq M L) (baseA _) ≤ puTrans h.le (Uq M T L) (baseA _) := by
      rw [hU, hW]
      exact imM_mono h.le inf_le_left
    have hUQ : puTrans h.le (Uq M T L) (baseA _) ≤ Qv (puAmalgam h.le) (baseB _) := by
      rw [hU, hQβ]
      exact imM_mono h.le ((Uq_le_Z0q h.L_le).trans (h.Z0q_le_pCoreOf.trans h.pCore_le))
    have hQs := qv_le_stab_of_isMVtx _ h20 hα hαβ
    have hUW : ¬ puTrans h.le (Uq M T L) (baseA _) ≤
        puTrans h.le (Uq M T L ⊓ Zq M L) (baseA _) := by
      rw [hU, hW, imM_le_imM_iff h.le (Uq_le h.L_le)]
      intro hle
      obtain ⟨v, hv⟩ := hR.surj (codeQ ⟨2, by decide⟩)
      have h1 : f v = 1 := (hR.ker v).mpr (hle v.val_mem).2
      rw [hv] at h1
      exact absurd ((codeQ_eq_one_iff _).mp h1) (by decide)
    obtain ⟨x, hx, hxW⟩ := exists_mem_botLayer (isPGroup_qv _ h20 hβ) hWU hUQ
      (hQs.trans (stab_le_normalizer_puTrans h.le (uqzq_normal h) _))
      (hQs.trans (stab_le_normalizer_puTrans h.le (uq_normal h) _)) hUW
    exact ⟨x, (mem_aSub h).mpr ⟨hx.1, hx.2.2.2.2⟩, hxW⟩
  have hAU : aSub h (baseA _) (baseB _) ≤ imM h.le (Uq M T L) := hU ▸ inf_le_left
  set A₀ := S33.pre h.le (aSub h (baseA _) (baseB _)) with hA₀
  have hA₀im : imM h.le A₀ = aSub h (baseA _) (baseB _) :=
    S33.imM_pre h.le (hAU.trans (imM_mono h.le (Uq_le h.L_le)))
  have hA₀U : A₀ ≤ Uq M T L := by
    rw [← imM_le_imM_iff h.le (S33.pre_le h.le _), hA₀im]
    exact hAU
  have hWA : Uq M T L ⊓ Zq M L ≤ A₀ := by
    rw [← imM_le_imM_iff h.le (inf_le_left.trans (Uq_le h.L_le)), hA₀im, ← hW]
    exact wt_le_aSub h hα hαβ
  have hAn : L ≤ Subgroup.normalizer (A₀ : Set G) := by
    refine le_normalizer_of_conj fun l hl a ha => ?_
    obtain ⟨m, hm, rfl⟩ := (S33.mem_pre_iff' h.le).mp ha
    have hlS : (puAmalgam h.le).ofA ⟨l, h.L_le hl⟩ ∈ stab (puAmalgam h.le) (baseA _) := by
      rw [puAmalgam.stab_baseA]
      exact ⟨⟨l, h.L_le hl⟩, Subgroup.mem_subgroupOf.mpr (h.L_le hl), rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hN hlS) _).mp hm
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact (S33.mem_pre_iff h.le _).mpr h1
  rcases hR.eq_or_eq_of_le_normalizer hWA hA₀U hAn with h1 | h1
  · apply hxW
    rw [hW, ← h1, hA₀im]
    exact hx
  ·
    obtain ⟨α', hc, hg⟩ := exists_isCritical_geo _ h20 hb0 hα hαβ
    obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp (ms22_iii _ h20 hb0 hC hc).2.2
    have hzβ : z ∈ Qv (puAmalgam h.le) (baseB _) := by
      rw [← hg]
      exact zm_le_qv_geo_one _ h20 hb0 hc hz
    rw [hQβ] at hzβ
    obtain ⟨t, ht, rfl⟩ := hzβ
    apply hzQ
    rw [hQ]
    refine (S33.ofA_mem_imM_iff h.le t).mpr ((hR.eq_one_iff_mem_pCoreOf
      (Subgroup.mem_subgroupOf.mp ht)).mp ((hR.eq_one_iff t).mpr fun u hu => ?_))
    have huA : (puAmalgam h.le).ofA ⟨u, Uq_le h.L_le hu⟩ ∈ aSub h (baseA _) (baseB _) := by
      rw [← hA₀im, h1]
      exact (S33.ofA_mem_imM_iff h.le _).mpr hu
    have h2 := ((mem_aSub h).mp huA).2 _ (by rw [hQβ]; exact ⟨t, ht, rfl⟩)
    rw [hW, ← map_commutatorElement, S33.ofA_mem_imM_iff] at h2
    exact h2.2

theorem not_stab_le_normalizer_aSub (hR : G2Rep h f φ) {γ ρ : Vtx (puAmalgam h.le)}
    (hγ : IsMVtx _ γ) (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) :
    ¬ stab (puAmalgam h.le) γ ≤
      Subgroup.normalizer (aSub h γ ρ : Set (puAmalgam h.le).Universal) := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ (PU.isMVtx_baseA _) (adj_baseA_baseB _)
    hγ hγρ
  rw [aSub_smul, stab_le_normalizer_map_iff]
  exact hR.not_stab_le_normalizer_aSub_base

theorem aSub_le_commutator (hR : G2Rep h f φ) (hX : Xq M = Z0q M T)
    (hW : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      imM h.le (Uq M T L ⊓ Zq M L) ≤
        ⁅ZM (puAmalgam h.le) (baseA (puAmalgam h.le)), ZM (puAmalgam h.le) α'⁆)
    {γ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) γ δ') :
    aSub h γ (geo (puAmalgam h.le) γ δ' 1) ≤
      ⁅XM (puAmalgam h.le) γ, XM (puAmalgam h.le) δ'⁆ := by
  rw [xm_eq h hX hc.1, xm_eq h hX (hc.isMVtx_right _ h.hyp20)]
  intro u hu
  obtain ⟨hu1, hu2⟩ := (mem_aSub h).mp hu
  exact hR.rEq hW hc u hu1 fun z hz => hu2 z (zm_le_qv_geo_one _ h.hyp20 h.critDist_pos hc hz)

theorem ms23_aSub (hR : G2Rep h f φ) (hX : Xq M = Z0q M T)
    (hW : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      imM h.le (Uq M T L ⊓ Zq M L) ≤
        ⁅ZM (puAmalgam h.le) (baseA (puAmalgam h.le)), ZM (puAmalgam h.le) α'⁆)
    (hb : 2 < critDist (puAmalgam h.le)) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ γ') :
    critDist (puAmalgam h.le) = 4 ∧ stab (puAmalgam h.le) (geo (puAmalgam h.le) γ γ' 2) ≤
      Subgroup.normalizer (aSub h γ (geo (puAmalgam h.le) γ γ' 1) :
        Set (puAmalgam h.le).Universal) := by
  have hγρ := adj_geo_one_of_isCritical _ h.critDist_pos hc
  have key := ms23 _ h.hyp20 hc.1 hγρ hb (h.gen23At hc.1 hγρ)
    (fun α' hc' _ => ⟨_, hR.zc23At hc'⟩) (qv_le_normalizer_aSub h hc.1 hγρ)
    (hR.not_stab_le_normalizer_aSub hc.1 hγρ)
    (fun δ' hd hgeo => by
      rw [← hgeo]
      exact hR.aSub_le_commutator hX hW hd)
  exact ⟨key.1, key.2 γ' hc rfl⟩

theorem lt_le_centralizer_aSub (hR : G2Rep h f φ) (hX : Xq M = Z0q M T)
    (hW : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      imM h.le (Uq M T L ⊓ Zq M L) ≤
        ⁅ZM (puAmalgam h.le) (baseA (puAmalgam h.le)), ZM (puAmalgam h.le) α'⁆)
    (hb : 2 < critDist (puAmalgam h.le)) {γ γ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ γ') :
    puTrans h.le L (geo (puAmalgam h.le) γ γ' 2) ≤ Subgroup.centralizer
      (aSub h γ (geo (puAmalgam h.le) γ γ' 1) : Set (puAmalgam h.le).Universal) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hb2 := two_le_critDist _ h20 hb0
  have hd : (puAmalgam h.le).treeGraph.dist γ γ' = critDist _ := hc.2.1
  set Aε := ⁅XM (puAmalgam h.le) γ, XM (puAmalgam h.le) γ'⁆ with hAεdef
  set μ := geo (puAmalgam h.le) γ γ' 2 with hμdef
  set ρ := geo (puAmalgam h.le) γ γ' 1 with hρdef
  have hερ : (puAmalgam h.le).treeGraph.Adj γ ρ := adj_geo_one_of_isCritical _ hb0 hc
  have hρμ : (puAmalgam h.le).treeGraph.Adj ρ μ := adj_geo _ (i := 1) (by omega)
  have hμ : IsMVtx _ μ := isMVtx_geo_two _ h20 hb0 hc
  have : Finite (Qv (puAmalgam h.le) ρ) :=
    finite_qv _ h20 ((isMVtx_iff_of_adj _ hερ).mp hc.1)
  have hAε : Aε ≤ XM _ γ := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((xm_le_qv_geo_one _ h20 hb0 hC hc).trans ((qv_le_stab_of_adj _ hερ.symm).trans
      (stab_le_normalizer_xm _ γ)))
  have hAε' : Aε ≤ XM _ γ' := commutator_xm_le_right _ h20 hb0 hC hc
  set S := Qv (puAmalgam h.le) γ ⊔ XM _ γ' with hSdef
  have hSρ : S ≤ Qv _ ρ := sup_le (qv_le_qv _ h20 hc.1 hερ) (xm_le_qv_geo_one _ h20 hb0 hC hc)
  have hSC : S ≤ Subgroup.centralizer (Aε : Set (puAmalgam h.le).Universal) := by
    refine sup_le ((qv_le_centralizer_xm _ γ).trans (Subgroup.centralizer_le hAε)) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (xm_le_centralizer _ γ' hx) y (xm_le_qv _ γ' (hAε' hy))
  have hSμ : ¬ S ≤ Qv _ μ := by
    intro hle
    have : Finite S := Finite.of_injective _ (Subgroup.inclusion_injective hSρ)
    have : Finite (Qv (puAmalgam h.le) μ) := Finite.of_injective _
      (Subgroup.inclusion_injective (qv_le_qv _ h20 hμ hρμ.symm))
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hc.1 hμ
    have hcard : Nat.card (Qv (puAmalgam h.le) μ) = Nat.card (Qv (puAmalgam h.le) γ) := by
      rw [← hg, qv_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hlt : Qv (puAmalgam h.le) γ < S :=
      lt_of_le_of_ne le_sup_left fun he =>
        xm_not_le_qv_of_isCritical h20 hb0 hC hc (he ▸ le_sup_right)
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := Subgroup.card_le_of_le hle
    omega
  obtain ⟨x, hxS, hxμ⟩ := Set.not_subset.mp hSμ
  have haR : aSub h γ ρ ≤ Aε := hR.aSub_le_commutator hX hW hc
  exact (h.puTrans_L_le_closure hμ hρμ.symm (hSρ hxS) hxμ).trans
    (closure_conj_le_centralizer (hR.ms23_aSub hX hW hb hc).2
      ((hSC.trans (Subgroup.centralizer_le haR)) hxS))

theorem vv_not_le (hR : G2Rep h f φ) (hb : 2 < critDist (puAmalgam h.le))
    {ε ε' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) ε ε') :
    ¬ Vv (puAmalgam h.le) ε ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) ε' ε 2) :=
  ms23_step3 _ h.hyp20 h.critDist_pos hb h.centHyp (fun _ _ hγ hγρ => h.gen23At hγ hγρ)
    (fun _ _ hc' => ⟨_, hR.zc23At hc'⟩) hc

end G2Rep

end CFSG.Quasithin.MS93.S38G
