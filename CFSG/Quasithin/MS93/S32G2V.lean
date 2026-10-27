module

public import CFSG.Quasithin.MS93.S32Crit
public import CFSG.Quasithin.MS93.S32Types
public import CFSG.Quasithin.MS93.S32G2M
public import CFSG.Quasithin.MS93.S32Main

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section CommChar

variable {Γ Γ' : Type*} [Group Γ] [Group Γ']

@[expose] def CommChar (U C Z : Subgroup Γ) : Prop :=
  ∀ v ∈ U, (v ∈ C ∧ v ≠ 1) ↔ (v ∈ ⁅Z, U⁆ ∧ ∀ e ∈ Z, ∀ u ∈ U, ⁅e, u⁆ ≠ v)

theorem commChar_map_iff {f : Γ →* Γ'} (hf : Function.Injective f) (U C Z : Subgroup Γ) :
    CommChar (U.map f) (C.map f) (Z.map f) ↔ CommChar U C Z := by
  have hmem : ∀ (H : Subgroup Γ) (x : Γ), f x ∈ H.map f ↔ x ∈ H := fun H x =>
    ⟨fun ⟨y, hy, he⟩ => hf he ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hpure : ∀ x : Γ, (∀ e ∈ Z.map f, ∀ u ∈ U.map f, ⁅e, u⁆ ≠ f x) ↔
      (∀ e ∈ Z, ∀ u ∈ U, ⁅e, u⁆ ≠ x) := by
    intro x
    constructor
    · intro H e he u hu hx
      exact H (f e) ⟨e, he, rfl⟩ (f u) ⟨u, hu, rfl⟩ (by rw [← map_commutatorElement, hx])
    · rintro H _ ⟨e, he, rfl⟩ _ ⟨u, hu, rfl⟩ hx
      rw [← map_commutatorElement] at hx
      exact H e he u hu (hf hx)
  constructor
  · intro H v hv
    have := H (f v) ⟨v, hv, rfl⟩
    rw [hmem, ← Subgroup.map_commutator, hmem, hpure, map_ne_one_iff f hf] at this
    exact this
  · rintro H _ ⟨v, hv, rfl⟩
    rw [hmem, ← Subgroup.map_commutator, hmem, hpure, map_ne_one_iff f hf]
    exact H v hv

theorem commutatorElement_mul_of_commute {e u c : Γ} (hce : c * e = e * c) :
    ⁅e, u * c⁆ = ⁅e, u⁆ := by
  have hci : c * e⁻¹ = e⁻¹ * c := (Commute.inv_right hce).eq
  simp only [commutatorElement_def, mul_inv_rev]
  calc e * (u * c) * e⁻¹ * (c⁻¹ * u⁻¹) = e * u * (c * e⁻¹ * c⁻¹) * u⁻¹ := by group
    _ = e * u * e⁻¹ * u⁻¹ := by rw [hci, mul_inv_cancel_right]

theorem exists_mul_eq_of_sup_eq {A B U : Subgroup Γ} (hUB : U ≤ B)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsup : U ⊔ (B ⊓ Subgroup.centralizer (A : Set Γ)) = B) {b : Γ} (hb : b ∈ B) :
    ∃ u ∈ U, ∃ c ∈ B ⊓ Subgroup.centralizer (A : Set Γ), u * c = b := by
  have hN : U ≤ Subgroup.normalizer
      ((B ⊓ Subgroup.centralizer (A : Set Γ) : Subgroup Γ) : Set Γ) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : u * x * u⁻¹ = x := by rw [hB _ (hUB hu) _ hx.1, mul_inv_cancel_right]
      rw [this]
      exact hx
    · intro hx
      have hxB : x ∈ B := by
        have := (B.mul_mem (B.mul_mem (B.inv_mem (hUB hu)) hx.1) (hUB hu))
        rwa [show u⁻¹ * (u * x * u⁻¹) * u = x by group] at this
      have : u * x * u⁻¹ = x := by rw [hB _ (hUB hu) _ hxB, mul_inv_cancel_right]
      rw [← this]
      exact hx
  have hb' : b ∈ (↑(U ⊔ (B ⊓ Subgroup.centralizer (A : Set Γ))) : Set Γ) := by rw [hsup]; exact hb
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hb'
  obtain ⟨u, hu, c, hc, he⟩ := hb'
  exact ⟨u, hu, c, hc, he⟩

theorem commutator_eq_of_sup_eq {A B U : Subgroup Γ} (hUB : U ≤ B)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsup : U ⊔ (B ⊓ Subgroup.centralizer (A : Set Γ)) = B) :
    ⁅A, U⁆ = ⁅A, B⁆ ∧ ∀ v : Γ, ((∃ e ∈ A, ∃ u ∈ U, ⁅e, u⁆ = v) ↔
      (∃ e ∈ A, ∃ b ∈ B, ⁅e, b⁆ = v)) := by
  have hcomm : ∀ e ∈ A, ∀ b ∈ B, ∃ u ∈ U, ⁅e, b⁆ = ⁅e, u⁆ := by
    intro e he b hb
    obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_eq_of_sup_eq hUB hB hsup hb
    exact ⟨u, hu, commutatorElement_mul_of_commute
      (Subgroup.mem_centralizer_iff.mp hc.2 e he).symm⟩
  refine ⟨le_antisymm (Subgroup.commutator_mono le_rfl hUB) ?_, fun v => ⟨?_, ?_⟩⟩
  · rw [Subgroup.commutator_le]
    intro e he b hb
    obtain ⟨u, hu, hcu⟩ := hcomm e he b hb
    rw [hcu]
    exact Subgroup.commutator_mem_commutator he hu
  · rintro ⟨e, he, u, hu, rfl⟩
    exact ⟨e, he, u, hUB hu, rfl⟩
  · rintro ⟨e, he, b, hb, rfl⟩
    obtain ⟨u, hu, hcu⟩ := hcomm e he b hb
    exact ⟨e, he, u, hu, hcu.symm⟩

end CommChar

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem uq_subgroupOf_normal (h : PUHyp M T L) : ((Uq M T L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Uq_le h.L_le)).2 (le_normalizer_Uq h.le_normalizer)

theorem uqzq_subgroupOf_normal (h : PUHyp M T L) :
    ((Uq M T L ⊓ Zq M L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans (Uq_le h.L_le))).2
    (le_normalizer_inf (le_normalizer_Uq h.le_normalizer) (le_normalizer_Zq h.le_normalizer))

theorem l_subgroupOf_normal (h : PUHyp M T L) : (L.subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer

theorem puTrans_inf_centralizer (h : PUHyp M T L) (g : (puAmalgam h.le).Universal) :
    puTrans h.le (Uq M T L) (g • baseA _) ⊓
        Subgroup.centralizer (puTrans h.le L (g • baseA _) : Set (puAmalgam h.le).Universal) =
      (imM h.le (Uq M T L ⊓ Zq M L)).map (MulAut.conj g).toMonoidHom := by
  rw [puTrans_smul_baseA (uq_subgroupOf_normal h), puTrans_smul_baseA (l_subgroupOf_normal h),
    PU.centralizer_map_mulEquiv, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← imM_inf_centralizer h.le _ h.L_le, ← h.Uq_inf_Zq]

theorem vertex_clause_of_bot (h : PUHyp M T L) (hC : fixV (autI h.isElemAbelian_Uq L) = ⊥)
    (α' : Vtx (puAmalgam h.le)) (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    imM h.le (Uq M T L ⊓ Zq M L) = puTrans h.le (Uq M T L) α' ⊓
        Subgroup.centralizer (puTrans h.le L α' : Set (puAmalgam h.le).Universal) ∧
      imM h.le (Uq M T L ⊓ Zq M L) ≤ ⁅ZM (puAmalgam h.le) (baseA _), ZM (puAmalgam h.le) α'⁆ := by
  have hbot : imM h.le (Uq M T L ⊓ Zq M L) = ⊥ := by
    rw [Uq_inf_Zq_eq_bot h hC, imM_eq_bot_iff h.le bot_le]
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ (hc.isMVtx_right _ h.hyp20)
  rw [puTrans_inf_centralizer h g, hbot, Subgroup.map_bot]
  exact ⟨rfl, bot_le⟩

@[expose] def CommCharAt (h : PUHyp M T L) (γ δ : Vtx (puAmalgam h.le)) : Prop :=
  CommChar (puTrans h.le (Uq M T L) γ) (puTrans h.le (Uq M T L ⊓ Zq M L) γ) (ZM _ δ)

theorem commCharAt_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (γ δ : Vtx (puAmalgam h.le)) : CommCharAt h (g • γ) (g • δ) ↔ CommCharAt h γ δ := by
  rw [CommCharAt, CommCharAt, puTrans_smul h.le (uq_subgroupOf_normal h),
    puTrans_smul h.le (uqzq_subgroupOf_normal h), zm_smul]
  exact commChar_map_iff (MulAut.conj g).injective _ _ _

theorem critIdx_of_pull (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    (hZT : ZM _ δ ≤ imM h.le T) :
    (critIdx h δ).1 = (pCoreOf 2 M).relIndex (pullM h (ZM _ δ)) ∧
      (critIdx h δ).2.1 =
        (Subgroup.centralizer (pullM h (ZM _ δ) : Set G)).relIndex (Uq M T L) := by
  set E := pullM h (ZM _ δ) with hE
  have hET : E ≤ T := pullM_le_T h hZT
  have hEim : imM h.le E = ZM _ δ := imM_pullM h (hZT.trans (imM_mono h.le h.le))
  have hZα : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  simp only [critIdx]
  rw [← hEim, hZα, relIndex_centralizer_imM h (hET.trans h.le) (Z0q_le M T),
    relIndex_centralizer_imM h (Uq_le h.L_le) (hET.trans h.le)]
  refine ⟨?_, rfl⟩
  have hinf : Subgroup.centralizer (Z0q M T : Set G) ⊓ E = pCoreOf 2 M ⊓ E := by
    rw [← h.centralizer_Z0q, inf_comm T (Subgroup.centralizer _), inf_assoc,
      inf_eq_right.2 hET]
  rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right]

theorem commChar_of_internal (h : PUHyp M T L) {E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (Uq M T L : Set G))
    (hint : ∀ v : IntMod (Uq M T L) h.isElemAbelian_Uq,
      (v ∈ fixV (autI h.isElemAbelian_Uq L) ∧ v ≠ 1) ↔
        (v ∈ commV (autI h.isElemAbelian_Uq E) ∧
          ∀ a ∈ autI h.isElemAbelian_Uq E, ∀ w, a w * w⁻¹ ≠ v)) :
    CommChar (Uq M T L) (Uq M T L ⊓ Zq M L) E := by
  set hU := h.isElemAbelian_Uq
  intro g hg
  have hv := hint (IntMod.mk hU ⟨g, hg⟩)
  have h1 : IntMod.mk hU ⟨g, hg⟩ ∈ fixV (autI hU L) ↔ g ∈ Uq M T L ⊓ Zq M L := by
    rw [← C124.mem_toG_iff_of_mem hU, toG_fixV_Uq h]
    rfl
  have h2 : IntMod.mk hU ⟨g, hg⟩ ≠ 1 ↔ g ≠ 1 := by
    constructor
    · intro hne h1
      apply hne
      apply IntMod.val_injective
      exact h1
    · intro hne h1
      apply hne
      exact congrArg IntMod.val h1
  have h3 : IntMod.mk hU ⟨g, hg⟩ ∈ commV (autI hU E) ↔ g ∈ ⁅E, Uq M T L⁆ := by
    rw [← C124.mem_toG_iff_of_mem hU, C124.toG_commV hU hEN]
    rfl
  have h4 : (∀ a ∈ autI hU E, ∀ w : IntMod (Uq M T L) hU, a w * w⁻¹ ≠ IntMod.mk hU ⟨g, hg⟩) ↔
      (∀ e ∈ E, ∀ u ∈ Uq M T L, ⁅e, u⁆ ≠ g) := by
    constructor
    · intro H e he u hu heu
      apply H _ (convI_mem_autI hU he (hEN he)) (IntMod.mk hU ⟨u, hu⟩)
      apply IntMod.val_injective
      rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]
      rw [commutatorElement_def] at heu
      exact heu
    · intro H a ha w haw
      obtain ⟨e, he, rfl⟩ := (mem_autI hU).1 ha
      apply H e he w.val w.val_mem
      have := congrArg IntMod.val haw
      rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val] at this
      rw [commutatorElement_def]
      exact this
  rw [← h1, ← h2, ← h3, ← h4]
  exact hv

theorem autI_pullM_offender (h : PUHyp M T L) (hN : NoStrongOffU h) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) δ) (hZT : ZM _ δ ≤ imM h.le T) :
    autI h.isElemAbelian_Uq (pullM h (ZM _ δ)) ≠ ⊥ ∧
      Nat.card (IntMod (Uq M T L) h.isElemAbelian_Uq) ≤
        Nat.card (autI h.isElemAbelian_Uq (pullM h (ZM _ δ))) *
          Nat.card ↥(fixQuot (autI h.isElemAbelian_Uq (pullM h (ZM _ δ)))
            (fixV (autI h.isElemAbelian_Uq L))) := by
  set hU := h.isElemAbelian_Uq
  set E := pullM h (ZM _ δ) with hE
  have hET : E ≤ T := pullM_le_T h hZT
  have hEim : imM h.le E = ZM _ δ := imM_pullM h (hZT.trans (imM_mono h.le h.le))
  have hEN : E ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hET.trans (h.le.trans (le_normalizer_Uq h.le_normalizer))
  refine ⟨fun hbot => ?_, ?_⟩
  · have hEC := (autI_eq_bot_iff hU hEN).1 hbot
    have hEQ : E ≤ pCoreOf 2 M := by
      rw [← (isSecW_Uq h).inf_centralizer_eq h]
      exact le_inf hET hEC
    have h3 := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
    apply h3.2.2
    rw [← hEim, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
    exact imM_mono h.le hEQ
  obtain ⟨e1, -⟩ := crit_eq h hN hc
  obtain ⟨i1, i2⟩ := critIdx_of_pull h hZT
  have hcardA : Nat.card (autI hU E) =
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) := by
    rw [(isSecW_Uq h).card_autI_of_le_T h hET, ← i1, e1, i2]
  have hcard := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) (Uq M T L)
  have hfix : Nat.card (fixV (autI hU E)) ≤
      Nat.card ↥(fixQuot (autI hU E) (fixV (autI hU L))) := by
    refine Subgroup.card_le_of_le fun v hv a ha => ?_
    rw [hv a ha, mul_inv_cancel]
    exact Subgroup.one_mem _
  calc Nat.card (IntMod (Uq M T L) hU) = Nat.card ↥(Uq M T L) := rfl
    _ = Nat.card (autI hU E) * Nat.card (fixV (autI hU E)) := by
        rw [card_fixV_autI hU hEN, hcardA, ← hcard, inf_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ hfix

theorem commCharAt_base (h : PUHyp M T L) (hN : NoStrongOffU h)
    (hcomm : ∀ A : Subgroup (MulAut (IntMod (Uq M T L) h.isElemAbelian_Uq)),
      A ≤ autI h.isElemAbelian_Uq M → A ≠ ⊥ → IsElemAbelian2 A →
      Nat.card (IntMod (Uq M T L) h.isElemAbelian_Uq) ≤
        Nat.card A * Nat.card ↥(fixQuot A (fixV (autI h.isElemAbelian_Uq L))) →
      ∀ v, (v ∈ fixV (autI h.isElemAbelian_Uq L) ∧ v ≠ 1) ↔
        (v ∈ commV A ∧ ∀ a ∈ A, ∀ w, a w * w⁻¹ ≠ v))
    {δ : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) δ) :
    CommCharAt h (baseA _) δ := by
  set hU := h.isElemAbelian_Uq
  obtain ⟨m, hm, hg⟩ := exists_stab_smul_geo h hc
  have hmα : m • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).mp hm
  have hc₀ : IsCritical _ (baseA _) (m • δ) := by
    have := (isCritical_smul _ m (baseA _) δ).2 hc
    rwa [hmα] at this
  suffices H : CommCharAt h (baseA _) (m • δ) by
    rw [← hmα, commCharAt_smul] at H
    exact H
  have hZT := zm_le_imM_T h hc₀ hg
  set E := pullM h (ZM _ (m • δ)) with hE
  have hET : E ≤ T := pullM_le_T h hZT
  have hEim : imM h.le E = ZM _ (m • δ) := imM_pullM h (hZT.trans (imM_mono h.le h.le))
  have hEab : IsElemAbelian 2 E := isElemAbelian_pullM h
    (isElemAbelian_zm _ h.hyp20 h.critDist_pos (hc₀.isMVtx_right _ h.hyp20))
  have hEN : E ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hET.trans (h.le.trans (le_normalizer_Uq h.le_normalizer))
  obtain ⟨hA1, hoff⟩ := autI_pullM_offender h hN hc₀ hZT
  have hint := hcomm (autI hU E) (autI_mono hU (hET.trans h.le)) hA1
    (isElemAbelian2_autI hU hEab hEN) hoff
  have hG := commChar_of_internal h hEN hint
  have hsub : ∀ K : Subgroup G, K ≤ M → (K.subgroupOf M).map M.subtype = K := fun K hK => by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hK]
  rw [CommCharAt, puTrans_baseA h.le (uq_subgroupOf_normal h),
    puTrans_baseA h.le (uqzq_subgroupOf_normal h), ← hEim, imM, imM, imM,
    commChar_map_iff (puAmalgam h.le).ofA_injective,
    ← commChar_map_iff M.subtype_injective, hsub _ (Uq_le h.L_le),
    hsub _ (inf_le_left.trans (Uq_le h.L_le)), hsub _ (hET.trans h.le)]
  exact hG

theorem zm_le_stab_of_critical (h : PUHyp M T L) {γ δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ γ δ) : ZM _ γ ≤ stab _ δ := by
  have hb := h.critDist_pos
  have hd : 0 < (puAmalgam h.le).treeGraph.dist δ γ := by
    rw [SimpleGraph.dist_comm, hc.2.1]
    exact hb
  have hadj := adj_geo_one _ hd
  refine (zm_le_qv_of_dist_lt _ hc.1 ?_).trans (qv_le_stab_of_adj _ hadj.symm)
  rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), SimpleGraph.dist_comm, hc.2.1]
  omega

theorem vertex_clause_of_comm (h : PUHyp M T L) (hN : NoStrongOffU h)
    (hch : ∀ δ, IsCritical (puAmalgam h.le) (baseA _) δ → CommCharAt h (baseA _) δ)
    (α' : Vtx (puAmalgam h.le)) (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    imM h.le (Uq M T L ⊓ Zq M L) = puTrans h.le (Uq M T L) α' ⊓
        Subgroup.centralizer (puTrans h.le L α' : Set (puAmalgam h.le).Universal) ∧
      imM h.le (Uq M T L ⊓ Zq M L) ≤ ⁅ZM (puAmalgam h.le) (baseA _), ZM (puAmalgam h.le) α'⁆ := by
  set X := puAmalgam h.le
  have hα' := hc.isMVtx_right _ h.hyp20
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hα'
  set δ' := g⁻¹ • baseA X with hδ'
  have hc' : IsCritical X (baseA _) δ' := by
    have h3 := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
    have := (isCritical_smul _ g⁻¹ (g • baseA _) (baseA _)).2 h3
    rwa [inv_smul_smul] at this
  have hgδ : g • δ' = baseA X := by rw [hδ', smul_inv_smul]
  have ch1 := hch _ hc
  rw [CommCharAt, puTrans_baseA h.le (uq_subgroupOf_normal h),
    puTrans_baseA h.le (uqzq_subgroupOf_normal h)] at ch1
  have ch2 := (commCharAt_smul h g (baseA _) δ').2 (hch _ hc')
  rw [hgδ, CommCharAt] at ch2
  have sup1 := zm_eq_sup_of_crit h hN hc
  have sup2 : puTrans h.le (Uq M T L) (g • baseA X) ⊔ (ZM X (g • baseA X) ⊓
      Subgroup.centralizer (ZM X (baseA X) : Set X.Universal)) = ZM X (g • baseA X) := by
    have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) (zm_eq_sup_of_crit h hN hc')
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ← PU.centralizer_map_mulEquiv, ← zm_smul, ← zm_smul, hgδ,
      ← puTrans_smul_baseA (uq_subgroupOf_normal h)] at this
    exact this
  have hab : ∀ δ : Vtx X, IsMVtx X δ → ∀ x ∈ ZM X δ, ∀ y ∈ ZM X δ, x * y = y * x :=
    fun δ hδ x hx y hy => congrArg Subtype.val
      ((isElemAbelian_zm _ h.hyp20 h.critDist_pos hδ).1.1.1 ⟨x, hx⟩ ⟨y, hy⟩)
  have hUα : imM h.le (Uq M T L) ≤ ZM X (baseA X) := by
    rw [puAmalgam.zm_baseA h.le]
    exact imM_mono h.le (Uq_le_Z0q h.L_le)
  have hUα' : puTrans h.le (Uq M T L) (g • baseA X) ≤ ZM X (g • baseA X) := by
    rw [puTrans_smul_baseA (uq_subgroupOf_normal h), zm_smul]
    exact Subgroup.map_mono hUα
  obtain ⟨com1, pure1⟩ := commutator_eq_of_sup_eq hUα (hab _ (isMVtx_baseA _)) sup1
  obtain ⟨com2, pure2⟩ := commutator_eq_of_sup_eq hUα' (hab _ hα') sup2
  have hRU : ⁅ZM X (g • baseA X), imM h.le (Uq M T L)⁆ ≤ imM h.le (Uq M T L) := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer ((zm_le_stab_of_critical h
      (ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc)).trans
      (stab_le_normalizer_imM h (le_normalizer_Uq h.le_normalizer)))
  have hRU' : ⁅ZM X (baseA X), puTrans h.le (Uq M T L) (g • baseA X)⁆ ≤
      puTrans h.le (Uq M T L) (g • baseA X) := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer ((zm_le_stab_of_critical h hc).trans
      (stab_le_normalizer_puTrans h.le (uq_subgroupOf_normal h) _))
  have hinv : ∀ v ∈ ZM X (baseA X), v⁻¹ = v := fun v hv =>
    inv_eq_of_mul_eq_one_right (by
      rw [← pow_two]
      exact (isElemAbelian_zm _ h.hyp20 h.critDist_pos (isMVtx_baseA _)).2 v hv)
  have hc'' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  have hRZ : ⁅ZM X (baseA X), ZM X (g • baseA X)⁆ ≤ ZM X (baseA X) :=
    commutator_le_left_of_le_normalizer ((zm_le_stab_of_critical h hc'').trans
      (stab_le_normalizer_zm _ _))
  have hR1 : ⁅ZM X (g • baseA X), imM h.le (Uq M T L)⁆ =
      ⁅ZM X (baseA X), ZM X (g • baseA X)⁆ := by
    rw [com1, Subgroup.commutator_comm]
  have key : ∀ v, (v ∈ imM h.le (Uq M T L ⊓ Zq M L) ∧ v ≠ 1) ↔
      (v ∈ puTrans h.le (Uq M T L ⊓ Zq M L) (g • baseA X) ∧ v ≠ 1) := by
    intro v
    constructor
    · rintro ⟨hv, hv1⟩
      have hvU : v ∈ imM h.le (Uq M T L) := imM_mono h.le inf_le_left hv
      obtain ⟨hvR, hvP⟩ := (ch1 v hvU).1 ⟨hv, hv1⟩
      have hvR' : v ∈ ⁅ZM X (baseA X), ZM X (g • baseA X)⁆ := hR1 ▸ hvR
      have hvU' : v ∈ puTrans h.le (Uq M T L) (g • baseA X) := hRU' (com2 ▸ hvR')
      refine (ch2 v hvU').2 ⟨com2 ▸ hvR', fun e he u hu heu => ?_⟩
      obtain ⟨e', he', z', hz', hez⟩ := (pure2 v).1 ⟨e, he, u, hu, heu⟩
      obtain ⟨e'', he'', u'', hu'', hez'⟩ := (pure1 v).2
        ⟨z', hz', e', he', by rw [← commutatorElement_inv, hez, hinv v (hRZ hvR')]⟩
      exact hvP e'' he'' u'' hu'' hez'
    · rintro ⟨hv, hv1⟩
      have hvU' : v ∈ puTrans h.le (Uq M T L) (g • baseA X) :=
        puTrans_mono h.le inf_le_left _ hv
      obtain ⟨hvR, hvP⟩ := (ch2 v hvU').1 ⟨hv, hv1⟩
      have hvR' : v ∈ ⁅ZM X (baseA X), ZM X (g • baseA X)⁆ := com2 ▸ hvR
      have hvU : v ∈ imM h.le (Uq M T L) := hRU (hR1 ▸ hvR')
      refine (ch1 v hvU).2 ⟨hR1 ▸ hvR', fun e he u hu heu => ?_⟩
      obtain ⟨e', he', z', hz', hez⟩ := (pure1 v).1 ⟨e, he, u, hu, heu⟩
      obtain ⟨e'', he'', u'', hu'', hez'⟩ := (pure2 v).2
        ⟨z', hz', e', he', by rw [← commutatorElement_inv, hez, hinv v (hRZ hvR')]⟩
      exact hvP e'' he'' u'' hu'' hez'
  have heq : imM h.le (Uq M T L ⊓ Zq M L) =
      puTrans h.le (Uq M T L ⊓ Zq M L) (g • baseA X) := by
    ext v
    by_cases hv1 : v = 1
    · rw [hv1]
      exact ⟨fun _ => Subgroup.one_mem _, fun _ => Subgroup.one_mem _⟩
    · exact ⟨fun hv => ((key v).1 ⟨hv, hv1⟩).1, fun hv => ((key v).2 ⟨hv, hv1⟩).1⟩
  refine ⟨?_, fun v hv => ?_⟩
  · rw [puTrans_inf_centralizer h g, ← puTrans_smul_baseA (uqzq_subgroupOf_normal h)]
    exact heq
  · by_cases hv1 : v = 1
    · rw [hv1]
      exact Subgroup.one_mem _
    · have hvU : v ∈ imM h.le (Uq M T L) := imM_mono h.le inf_le_left hv
      exact hR1 ▸ ((ch1 v hvU).1 ⟨hv, hv1⟩).1

theorem s32PartG2Vertex_of (hG2C : MS15G2Comm) (hSQ : SQTKQuot) (hT : TypeFacts) :
    S32PartG2Vertex := by
  intro G _ _ M T L h hgd hcase α' hc
  rcases hcase with hC | ⟨hC, hirr, hcase⟩
  · exact vertex_clause_of_bot h hC α' hc
  set hU := h.isElemAbelian_Uq
  have hFF := h.isFFModule_of_le_Z0q (isSecW_Uq h) (Uq_le_Z0q h.L_le)
  have h15 := (isSecW_Uq h).ms15Hyp h hSQ (commV_autI_Uq h) hC hirr hFF
  have hL : Nat.card (Lstar L) = 6048 := by
    obtain ⟨F, iF, fF, hF, π, hπ⟩ := hgd
    exact card_lstar_of_g2d (isSecW_Uq h) h hT hF hπ
  obtain ⟨n, hn, hg, -⟩ | ⟨-, -, hX1, -⟩ := id hcase
  · exfalso
    obtain ⟨F, iF, fF, hF, π, hπ⟩ := hg
    obtain ⟨hn2, hc⟩ := card_lstar_of_g2 (isSecW_Uq h) h hT hF hπ
    exact (ordG2_ne (by omega)).2.2 (hc.symm.trans hL)
  have hN : NoStrongOffU h := fun A hA hAe => card_mul_card_fixV_le_g2_two hX1 hA hAe
  exact vertex_clause_of_comm h hN (fun δ hδ => commCharAt_base h hN
    (fun A hAX hA1 hAe hoff => hG2C _ IntMod.sq_eq_one _ _ h15 hcase A hAX hA1 hAe hoff) hδ)
    α' hc

end CFSG.Quasithin.MS93.S32
