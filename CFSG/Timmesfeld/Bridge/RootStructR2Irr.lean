module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManySmall
public import CFSG.Timmesfeld.Bridge.RootStructR2ManySetting
public import CFSG.Timmesfeld.Bridge.RootStructR2IrrForm

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped commutatorElement

namespace RootIrr

open RootMany

variable {G : Type} [Group G] {D : Set G}

@[expose] def comSub (D : Set G) (a d : G) : Subgroup G :=
  ⁅nCore D a, lineGroup D a d⁆ ⊔ rootGroup D a

variable [Finite G] (C : ThinGateCounter G D) {q : ℕ} (K : ThinGateCount G D q 2 2) {a d : G}
  (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)

section Basic

include C K ha hd had hadD hdT

omit [Finite G] K ha hd had hadD hdT in
theorem comm_mem_nCore {r : G} (hr : r ∈ lineGroup D a d) {m : G} (hm : m ∈ nCore D a) :
    r * m * r⁻¹ * m⁻¹ ∈ nCore D a :=
  Subgroup.mul_mem _ (conj_mem_nCore_of_mem_lineGroup C hr hm) (Subgroup.inv_mem _ hm)

omit [Finite G] K ha hd had hadD hdT in
theorem commutator_le_nCore : ⁅nCore D a, lineGroup D a d⁆ ≤ nCore D a := by
  rw [Subgroup.commutator_le]
  intro m hm r hr
  rw [commutatorElement_def]
  have := Subgroup.inv_mem _ (comm_mem_nCore C hr hm)
  rw [show (r * m * r⁻¹ * m⁻¹)⁻¹ = m * r * m⁻¹ * r⁻¹ by group] at this
  exact this

omit [Finite G] K hadD hdT in
theorem comSub_le : comSub D a d ≤ nCore D a :=
  sup_le (commutator_le_nCore C) (rootGroup_le_nCore' C ha hd had)

omit [Finite G] C K ha hd had hadD hdT in
theorem rootGroup_le_comSub : rootGroup D a ≤ comSub D a d := le_sup_right

omit [Finite G] C K ha hd had hadD hdT in
theorem comm_mem_comSub {r : G} (hr : r ∈ lineGroup D a d) {m : G} (hm : m ∈ nCore D a) :
    r * m * r⁻¹ * m⁻¹ ∈ comSub D a d := by
  have h1 := Subgroup.commutator_mem_commutator hm hr
  have h2 := Subgroup.inv_mem _ h1
  rw [commutatorElement_def, show (m * r * m⁻¹ * r⁻¹)⁻¹ = r * m * r⁻¹ * m⁻¹ by group] at h2
  exact Subgroup.mem_sup_left h2

omit [Finite G] K ha hd had hadD hdT in
theorem conj_mem_comSub {r : G} (hr : r ∈ lineGroup D a d) {b : G} (hb : b ∈ comSub D a d) :
    r * b * r⁻¹ ∈ comSub D a d := by
  have hle : (comSub D a d).map (MulAut.conj r).toMonoidHom ≤ comSub D a d := by
    rw [comSub, Subgroup.map_sup, Subgroup.map_commutator]
    refine sup_le_sup (Subgroup.commutator_mono ?_ ?_) ?_
    · rintro _ ⟨m, hm, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact conj_mem_nCore_of_mem_lineGroup C hr hm
    · rintro _ ⟨s, hs, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hr hs) (Subgroup.inv_mem _ hr)
    · rintro _ ⟨α, hα, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact conj_mem_rootGroup_of_mem_lineGroup C hr hα
  exact hle ⟨b, hb, rfl⟩

omit [Finite G] K in
theorem commute_of_mem_lineGroup' {r : G} (hr : r ∈ lineGroup D a d) {α : G}
    (hα : α ∈ rootGroup D a) : Commute r α :=
  (lineSetting_of_counter C).commute_of_mem_lineGroup ha hd had hadD hdT hr hα

theorem secHyp_of {E A' : Subgroup G} (hA : rootGroup D a ≤ A') (hAE : A' ≤ E)
    (hE : E ≤ nCore D a) (hEn : ∀ r ∈ lineGroup D a d, ∀ e ∈ E, r * e * r⁻¹ ∈ E)
    (hAn : ∀ r ∈ lineGroup D a d, ∀ x ∈ A', r * x * r⁻¹ ∈ A') :
    SecHyp (lineGroup D a d) (nCore D a) E A' where
  le := hAE
  le_R := hE.trans (secHyp_nCore C K ha hd had hadD hdT).le_R
  conj_E := hEn
  conj_A := hAn
  comm := fun x hx y hy => hA ((secHyp_nCore C K ha hd had hadD hdT).comm x (hE hx) y (hE hy))
  sq := fun x hx => hA ((secHyp_nCore C K ha hd had hadD hdT).sq x (hE hx))
  ker := fun k hk e he => hA ((secHyp_nCore C K ha hd had hadD hdT).ker k hk e (hE he))

theorem secHyp_comSub : SecHyp (lineGroup D a d) (nCore D a) (comSub D a d) (rootGroup D a) :=
  secHyp_of C K ha hd had hadD hdT le_rfl rootGroup_le_comSub (comSub_le C ha hd had)
    (fun _ hr _ hb => conj_mem_comSub C hr hb)
    (fun _ hr _ hα => conj_mem_rootGroup_of_mem_lineGroup C hr hα)

theorem exists_comm_not_mem : ∃ r ∈ lineGroup D a d, ∃ b ∈ comSub D a d,
    r * b * r⁻¹ * b⁻¹ ∉ rootGroup D a := by
  by_contra! h
  obtain ⟨m, hm, -, -, f, hf, hker⟩ := exists_l2 C K ha hd had hadD hdT
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  obtain ⟨x, hx, c, hc, hxc⟩ := exists_conj_mul_inv_not_mem C ha hd had hadD hdT
    (three_le_ncard_rootLines C K ha)
  exact hxc ((secHyp_nCore C K ha hd had hadD hdT).comm_mem f hf hker hm hF
    (fun _ hr _ he => comm_mem_comSub hr he) h hx hc)

theorem le_card_comSub : q ^ 5 ≤ Nat.card (comSub D a d) := by
  obtain ⟨r, hr, b, hb, hrb⟩ := exists_comm_not_mem C K ha hd had hadD hdT
  obtain ⟨m, hm, hqm, -, f, hf, hker⟩ := exists_l2 C K ha hd had hadD hdT
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have h1 := (secHyp_comSub C K ha hd had hadD hdT).sq_mul_card_le f hf hker hm hF hr hb hrb
  rw [hqm, K.card_rootGroup a ha] at h1
  calc q ^ 5 = (q ^ 2) ^ 2 * q := by ring
    _ ≤ _ := h1

theorem exists_mem_rootGroup_comSub (hM : Nat.card (nCore D a) < q ^ 6) :
    ∃ δ ∈ rootGroup D d, δ ∈ comSub D a d ∧ δ ≠ 1 := by
  by_contra! h
  have hLS := lineSetting_of_counter C
  have hdM : rootGroup D d ≤ nCore D a :=
    le_sup_right.trans (hLS.sup_rootGroup_le_nCore ha hd had)
  let N := (comSub D a d).subgroupOf (nCore D a)
  let φ : ↥(rootGroup D d) → ↥(nCore D a) ⧸ N :=
    fun δ => ((⟨δ, hdM δ.2⟩ : ↥(nCore D a)) : ↥(nCore D a) ⧸ N)
  have hφ : Function.Injective φ := by
    intro δ₁ δ₂ h12
    have h12' := QuotientGroup.eq.1 h12
    rw [Subgroup.mem_subgroupOf] at h12'
    have h' := h _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ δ₁.2) δ₂.2) (by simpa using h12')
    exact Subtype.ext (inv_mul_eq_one.1 h')
  have h1 := Nat.card_le_card_of_injective φ hφ
  rw [K.card_rootGroup d hd] at h1
  have h2 := Subgroup.card_mul_index N
  have h3 : Nat.card N = Nat.card (comSub D a d) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (comSub_le C ha hd had)).toEquiv
  have h4 := le_card_comSub C K ha hd had hadD hdT
  rw [h3] at h2
  have : q ^ 6 ≤ Nat.card (nCore D a) :=
    calc q ^ 6 = q ^ 5 * q := by ring
      _ ≤ Nat.card (comSub D a d) * N.index := Nat.mul_le_mul h4 h1
      _ = Nat.card (nCore D a) := h2
  omega

end Basic

section Cent

include C ha hd had hadD hdT

omit [Finite G] in
theorem commute_of_comm_mem {c : G} (hc : c ∈ nCore D a)
    (hcR : ∀ r ∈ lineGroup D a d, r * c * r⁻¹ * c⁻¹ ∈ rootGroup D a) {b : G}
    (hb : b ∈ comSub D a d) : Commute c b := by
  have hNC := nCoreCommutatorInRoot_of_hyp C.hyp C.closure
  have hAA : ∀ α ∈ rootGroup D a, ∀ β ∈ rootGroup D a, Commute α β := fun α hα β hβ =>
    commute_of_mem_rootGroup_of_commute' ha hα hβ (Commute.refl a)
  have hle : comSub D a d ≤ Subgroup.centralizer {c} := by
    refine sup_le ?_ fun α hα => ?_
    · rw [Subgroup.commutator_le]
      intro m hm r hr
      rw [commutatorElement_def, Subgroup.mem_centralizer_singleton_iff]
      have he : c * m * c⁻¹ * m⁻¹ ∈ rootGroup D a := hNC a ha c hc m hm
      have hβ : (r * c * r⁻¹ * c⁻¹)⁻¹ ∈ rootGroup D a := Subgroup.inv_mem _ (hcR r hr)
      set e := c * m * c⁻¹ * m⁻¹ with he_def
      set β := (r * c * r⁻¹ * c⁻¹)⁻¹ with hβ_def
      have hem : c * m * c⁻¹ = e * m := by rw [he_def]; group
      have hβr : c * r * c⁻¹ = β * r := by rw [hβ_def]; group
      have hme : Commute e m := (commute_of_mem_nCore_of_mem_rootGroup hm he).symm
      have hmβ : Commute β m := (commute_of_mem_nCore_of_mem_rootGroup hm hβ).symm
      have hre : Commute e r := (commute_of_mem_lineGroup' C ha hd had hadD hdT hr he).symm
      have hrβ : Commute β r := (commute_of_mem_lineGroup' C ha hd had hadD hdT hr hβ).symm
      have heβ : Commute e β := hAA _ he _ hβ
      have h1 : Commute e (m * (β * r) * m⁻¹) :=
        (hme.mul_right (heβ.mul_right hre)).mul_right hme.inv_right
      have h2 : Commute β (m * r * m⁻¹ * r⁻¹) :=
        ((hmβ.mul_right hrβ).mul_right hmβ.inv_right).mul_right hrβ.inv_right
      have key : c * (m * r * m⁻¹ * r⁻¹) * c⁻¹ = m * r * m⁻¹ * r⁻¹ :=
        calc c * (m * r * m⁻¹ * r⁻¹) * c⁻¹ =
            (c * m * c⁻¹) * (c * r * c⁻¹) * (c * m * c⁻¹)⁻¹ * (c * r * c⁻¹)⁻¹ := by group
          _ = e * (m * (β * r) * m⁻¹) * e⁻¹ * (r⁻¹ * β⁻¹) := by rw [hem, hβr]; group
          _ = m * (β * r) * m⁻¹ * (r⁻¹ * β⁻¹) := by rw [h1.eq, mul_inv_cancel_right]
          _ = (m * β) * r * m⁻¹ * r⁻¹ * β⁻¹ := by group
          _ = β * (m * r * m⁻¹ * r⁻¹) * β⁻¹ := by rw [← hmβ.eq]; group
          _ = m * r * m⁻¹ * r⁻¹ := by rw [h2.eq, mul_inv_cancel_right]
      exact (mul_inv_eq_iff_eq_mul.1 key).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_mem_nCore_of_mem_rootGroup hc hα).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hb)).symm

include K in
theorem commute_of_comm_mem_of_mem_line (hM : Nat.card (nCore D a) < q ^ 6) {c : G}
    (hc : c ∈ nCore D a) (hcR : ∀ r ∈ lineGroup D a d, r * c * r⁻¹ * c⁻¹ ∈ rootGroup D a)
    {t : G} (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute c t := by
  have hLS := lineSetting_of_counter C
  have hD := C.hyp.root
  have hclass := C.hyp.isClass
  have hNC := nCoreCommutatorInRoot_of_hyp C.hyp C.closure
  have hdM : rootGroup D d ≤ nCore D a :=
    le_sup_right.trans (hLS.sup_rootGroup_le_nCore ha hd had)
  have hinf : rootGroup D a ⊓ rootGroup D d = ⊥ :=
    rootGroup_inf_eq_bot_of_rootClosure hD C.closure ha hd fun h' =>
      hdT (h' ▸ mem_rootSet_self hd)
  obtain ⟨δ, hδd, hδB, hδ1⟩ := exists_mem_rootGroup_comSub C K ha hd had hadD hdT hM
  have hcδ : Commute c δ := commute_of_comm_mem C ha hd had hadD hdT hc hcR hδB
  have hδT : δ ∈ rootSet D d := mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure hd hδd hδ1
  have hAδ : rootGroup D δ = rootGroup D d := rootGroup_eq_of_mem hδT
  have hcd : ∀ s ∈ rootGroup D d, Commute c s := by
    intro s hs
    have h1 : c * s * c⁻¹ ∈ rootGroup D d := by
      have := conj_mem_rootGroup_of_commute hclass hcδ (by rw [hAδ]; exact hs)
      rwa [hAδ] at this
    have h2 : c * s * c⁻¹ * s⁻¹ ∈ rootGroup D a ⊓ rootGroup D d :=
      ⟨hNC a ha c hc s (hdM hs), Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hs)⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)
  have hle : rootGroup D a ⊔ rootGroup D d ≤ Subgroup.centralizer {c} := by
    refine sup_le (fun α hα => ?_) fun s hs => ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_of_mem_nCore_of_mem_rootGroup hc hα).symm.eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcd s hs).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle ht)).symm

include K in
theorem commute_of_comm_mem_of_mem_rootLines (hM : Nat.card (nCore D a) < q ^ 6) {c : G}
    (hc : c ∈ nCore D a) (hcR : ∀ r ∈ lineGroup D a d, r * c * r⁻¹ * c⁻¹ ∈ rootGroup D a)
    {L : Subgroup G} (hL : L ∈ rootLines D a) {t : G} (ht : t ∈ L) : Commute c t := by
  have hLS := lineSetting_of_counter C
  have h3 := three_le_ncard_rootLines C K ha
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  by_cases hLT : L = rootGroup D a ⊔ rootGroup D d
  · subst hLT
    exact commute_of_comm_mem_of_mem_line C K ha hd had hadD hdT hM hc hcR ht
  obtain ⟨L₀, hL₀, hL₀T, hL₀L⟩ :=
    exists_mem_rootLines_ne_ne (L₁ := rootGroup D a ⊔ rootGroup D d) (L₂ := L) h3
  obtain ⟨x, hx, hxT⟩ :=
    hLS.exists_mem_lineRadical_map_conj_eq ha hL₀ hT hL (Ne.symm hL₀T) (Ne.symm hL₀L)
  have hxR : x ∈ lineGroup D a d := hLS.lineRadical_le_lineGroup ha hd had hadD hdT h3 hL₀ hx
  rw [← hxT] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  have hc' : x⁻¹ * c * x⁻¹⁻¹ ∈ nCore D a :=
    conj_mem_nCore_of_mem_lineGroup C (Subgroup.inv_mem _ hxR) hc
  have hcR' : ∀ r ∈ lineGroup D a d,
      r * (x⁻¹ * c * x⁻¹⁻¹) * r⁻¹ * (x⁻¹ * c * x⁻¹⁻¹)⁻¹ ∈ rootGroup D a := by
    intro r hr
    have hxr : x * r * x⁻¹ ∈ lineGroup D a d :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxR hr) (Subgroup.inv_mem _ hxR)
    have := conj_mem_rootGroup_of_mem_lineGroup C (Subgroup.inv_mem _ hxR) (hcR _ hxr)
    convert this using 1
    group
  have h1 := commute_of_comm_mem_of_mem_line C K ha hd had hadD hdT hM hc' hcR' ht'
  have h2 := (Commute.conj_iff x).2 h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  convert h2 using 1
  group

include K in
theorem mem_rootGroup_of_comm_mem (hM : Nat.card (nCore D a) < q ^ 6)
    (hZ : ∀ z ∈ nCore D a, (∀ m ∈ nCore D a, Commute z m) → z ∈ rootGroup D a) {c : G}
    (hc : c ∈ nCore D a) (hcR : ∀ r ∈ lineGroup D a d, r * c * r⁻¹ * c⁻¹ ∈ rootGroup D a) :
    c ∈ rootGroup D a := by
  have hLS := lineSetting_of_counter C
  refine hZ c hc fun m hm => ?_
  have hle : nCore D a ≤ Subgroup.centralizer {c} := by
    rw [hLS.nCore_eq_closure ha, Subgroup.closure_le]
    rintro x ⟨hxD, hax⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    by_cases hxT : x ∈ rootSet D a
    · exact (commute_of_mem_nCore_of_mem_rootGroup hc
        (rootSet_subset_rootGroup D a hxT)).symm.eq
    rcases hLS.mem_rootSet_or_collinear ha hxD hax.symm with h | ⟨hax', haxD⟩
    · exact absurd h hxT
    have hL : rootGroup D a ⊔ rootGroup D x ∈ rootLines D a := ⟨x, hxD, hax', haxD, hxT, rfl⟩
    exact (commute_of_comm_mem_of_mem_rootLines C K ha hd had hadD hdT hM hc hcR hL
      (right_mem_line hxD)).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hm)).symm

end Cent

section Irr

include C K ha hd had hadD hdT

theorem eq_or_eq_of_le_comSub (hM : Nat.card (nCore D a) < q ^ 6)
    (hZ : ∀ z ∈ nCore D a, (∀ m ∈ nCore D a, Commute z m) → z ∈ rootGroup D a)
    {B' : Subgroup G} (hAB : rootGroup D a ≤ B') (hBB : B' ≤ comSub D a d)
    (hBn : ∀ r ∈ lineGroup D a d, ∀ b ∈ B', r * b * r⁻¹ ∈ B') :
    B' = rootGroup D a ∨ B' = comSub D a d := by
  have hBM := comSub_le C ha hd had
  by_cases htriv : ∀ r ∈ lineGroup D a d, ∀ b ∈ B', r * b * r⁻¹ * b⁻¹ ∈ rootGroup D a
  · exact Or.inl (le_antisymm (fun b hb => mem_rootGroup_of_comm_mem C K ha hd had hadD hdT hM
      hZ (hBM (hBB hb)) fun r hr => htriv r hr b hb) hAB)
  push Not at htriv
  obtain ⟨r, hr, b, hb, hrb⟩ := htriv
  obtain ⟨m, hm, hqm, -, f, hf, hker⟩ := exists_l2 C K ha hd had hadD hdT
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hAn : ∀ r ∈ lineGroup D a d, ∀ x ∈ rootGroup D a, r * x * r⁻¹ ∈ rootGroup D a :=
    fun _ hr _ hx => conj_mem_rootGroup_of_mem_lineGroup C hr hx
  have h1 := (secHyp_of C K ha hd had hadD hdT le_rfl hAB (hBB.trans hBM) hBn
    hAn).sq_mul_card_le f hf hker hm hF hr hb hrb
  have htriv2 : ∀ r ∈ lineGroup D a d, ∀ b ∈ comSub D a d, r * b * r⁻¹ * b⁻¹ ∈ B' := by
    by_contra! h
    obtain ⟨r', hr', b', hb', hrb'⟩ := h
    have h2 := (secHyp_of C K ha hd had hadD hdT hAB hBB hBM
      (fun _ hr _ hb => conj_mem_comSub C hr hb) hBn).sq_mul_card_le f hf hker hm hF hr' hb' hrb'
    have h3 : Nat.card (comSub D a d) ≤ Nat.card (nCore D a) := Subgroup.card_le_of_le hBM
    rw [hqm, K.card_rootGroup a ha] at h1
    rw [hqm] at h2
    have hq := two_le_q C K ha
    have : q ^ 9 ≤ Nat.card (nCore D a) :=
      calc q ^ 9 = (q ^ 2) ^ 2 * ((q ^ 2) ^ 2 * q) := by ring
        _ ≤ (q ^ 2) ^ 2 * Nat.card B' := Nat.mul_le_mul_left _ h1
        _ ≤ Nat.card (comSub D a d) := h2
        _ ≤ Nat.card (nCore D a) := h3
    have : q ^ 6 ≤ q ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  right
  refine le_antisymm hBB (sup_le ?_ hAB)
  rw [Subgroup.commutator_le]
  intro e he s hs
  have h2 := (secHyp_of C K ha hd had hadD hdT hAB (hBB.trans hBM) le_rfl
    (fun _ hr _ he => conj_mem_nCore_of_mem_lineGroup C hr he) hBn).comm_mem f hf hker hm hF
    (fun _ hr _ he => comm_mem_comSub hr he) htriv2 hs he
  rw [commutatorElement_def]
  have h3 := Subgroup.inv_mem _ h2
  rwa [show (s * e * s⁻¹ * e⁻¹)⁻¹ = e * s * e⁻¹ * s⁻¹ by group] at h3

theorem comSub_eq (hM : Nat.card (nCore D a) < q ^ 6)
    (hZ : ∀ z ∈ nCore D a, (∀ m ∈ nCore D a, Commute z m) → z ∈ rootGroup D a) :
    comSub D a d = nCore D a := by
  have hLS := lineSetting_of_counter C
  have hD := C.hyp.root
  have hclass := C.hyp.isClass
  have hNC := nCoreCommutatorInRoot_of_hyp C.hyp C.closure
  have hBM := comSub_le C ha hd had
  have hAB : rootGroup D a ≤ comSub D a d := rootGroup_le_comSub
  have hAA : ∀ α ∈ rootGroup D a, ∀ β ∈ rootGroup D a, Commute α β := fun α hα β hβ =>
    commute_of_mem_rootGroup_of_commute' ha hα hβ (Commute.refl a)
  have hconjB : ∀ r ∈ lineGroup D a d, ∀ b ∈ comSub D a d, r⁻¹ * b * r ∈ comSub D a d :=
    fun r hr b hb => by
      have := conj_mem_comSub C (Subgroup.inv_mem _ hr) hb
      rwa [inv_inv] at this
  obtain ⟨δ, hδd, hδB, hδ1⟩ := exists_mem_rootGroup_comSub C K ha hd had hadD hdT hM
  have hδT : δ ∈ rootSet D d := mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure hd hδd hδ1
  have hinf : rootGroup D a ⊓ rootGroup D d = ⊥ :=
    rootGroup_inf_eq_bot_of_rootClosure hD C.closure ha hd fun h' =>
      hdT (h' ▸ mem_rootSet_self hd)
  have hδA : δ ∉ rootGroup D a := fun h' => hδ1 (by
    have : δ ∈ rootGroup D a ⊓ rootGroup D d := ⟨h', hδd⟩
    rwa [hinf, Subgroup.mem_bot] at this)
  obtain ⟨x, hx, hax, haxD, hxT⟩ := exists_point C ha hd had hadD hdT
  have hxa : x ∉ rootSet D a := fun h' =>
    hxT (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h'))
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  have hTx : rootGroup D a ⊔ rootGroup D x ∈ rootLines D a := ⟨x, hx, hax, haxD, hxa, rfl⟩
  have hTTx : rootGroup D a ⊔ rootGroup D x ≠ rootGroup D a ⊔ rootGroup D d := fun h' =>
    hxT (h' ▸ right_mem_line hx)
  have h3 := three_le_ncard_rootLines C K ha
  obtain ⟨L₀, hL₀, hL₀T, hL₀Tx⟩ := exists_mem_rootLines_ne_ne
    (L₁ := rootGroup D a ⊔ rootGroup D d) (L₂ := rootGroup D a ⊔ rootGroup D x) h3
  obtain ⟨r₀, hr₀, hr₀T⟩ :=
    hLS.exists_mem_lineRadical_map_conj_eq ha hL₀ hT hTx (Ne.symm hL₀T) (Ne.symm hL₀Tx)
  have hr₀R : r₀ ∈ lineGroup D a d := hLS.lineRadical_le_lineGroup ha hd had hadD hdT h3 hL₀ hr₀
  obtain ⟨l₀, hl₀_def⟩ : ∃ l₀, l₀ = r₀ * δ * r₀⁻¹ := ⟨_, rfl⟩
  have hl₀B : l₀ ∈ comSub D a d := hl₀_def ▸ conj_mem_comSub C hr₀R hδB
  have hl₀D : l₀ ∈ D := hl₀_def ▸ conj_mem_of_isClass hclass r₀ hδT.1
  have hl₀Tx : l₀ ∈ rootGroup D a ⊔ rootGroup D x := by
    rw [← hr₀T, hl₀_def]
    exact ⟨δ, Subgroup.mem_sup_right hδd, rfl⟩
  have hal₀ : Commute a l₀ := commute_of_mem_sup_rootGroup ha hx hax (left_mem_line ha) hl₀Tx
  have hl₀A : l₀ ∉ rootGroup D a := fun h' => hδA (by
    have := conj_mem_rootGroup_of_mem_lineGroup C (Subgroup.inv_mem _ hr₀R) h'
    rwa [hl₀_def, show r₀⁻¹ * (r₀ * δ * r₀⁻¹) * r₀⁻¹⁻¹ = δ by group] at this)
  have hl₀a : l₀ ∉ rootSet D a := fun h' => hl₀A (rootSet_subset_rootGroup D a h')
  have hl₀T : l₀ ∉ rootGroup D a ⊔ rootGroup D d := fun h' => hTTx (by
    rw [← hLS.sup_rootGroup_eq_of_mem_sup ha hl₀D hd hal₀ hl₀a had hadD hdT h',
      hLS.sup_rootGroup_eq_of_mem_sup ha hl₀D hx hal₀ hl₀a hax haxD hxa hl₀Tx])
  have h4 := orderOf_mul_eq_four_of_not_mem_line hD hLS.lineCentralizerEq ha hd had hadD hdT
    (hLS.lineTI ha hd had hadD hdT) hl₀D hal₀ hl₀T
  have hnc : ¬ Commute δ l₀ := fun h' => not_commute_of_orderOf_mul_eq_four
    (hD.mul_self_eq_one hl₀D) (hD.mul_self_eq_one hd) h4 ((hδT.2 l₀ hl₀D).1 h').symm
  have hδl₀ : δ * l₀ * δ⁻¹ * l₀⁻¹ ∈ rootGroup D a := hNC a ha δ (hBM hδB) l₀ (hBM hl₀B)
  have hδl₀1 : δ * l₀ * δ⁻¹ * l₀⁻¹ ≠ 1 := fun h' =>
    hnc (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h'))
  obtain ⟨lam, hlam, hlam0⟩ := exists_lam (rootGroup D a) hAA
    (fun _ hα => mul_self_eq_one_of_mem_rootGroup hD ha hα) hδl₀ hδl₀1
  have hFH : FormHyp (nCore D a) (rootGroup D a) (comSub D a d) :=
    ⟨hAB, hBM, fun α hα m hm => (commute_of_mem_nCore_of_mem_rootGroup hm hα).symm,
      fun m hm m' hm' => hNC a ha m hm m' hm',
      fun m hm => mul_self_mem_rootGroup_of_mem_nCore C.hyp C.closure ha hm⟩
  have hconj : ∀ r ∈ lineGroup D a d, ∀ m ∈ nCore D a, ∀ b ∈ nCore D a,
      lam (r * m * r⁻¹ * b * (r * m * r⁻¹)⁻¹ * b⁻¹) =
        lam (m * (r⁻¹ * b * r) * m⁻¹ * (r⁻¹ * b * r)⁻¹) := by
    intro r hr m hm b hb
    have hb' : r⁻¹ * b * r ∈ nCore D a := by
      have := conj_mem_nCore_of_mem_lineGroup C (Subgroup.inv_mem _ hr) hb
      rwa [inv_inv] at this
    have hα := hNC a ha m hm _ hb'
    have e : r * m * r⁻¹ * b * (r * m * r⁻¹)⁻¹ * b⁻¹ =
        r * (m * (r⁻¹ * b * r) * m⁻¹ * (r⁻¹ * b * r)⁻¹) * r⁻¹ := by group
    rw [e, (commute_of_mem_lineGroup' C ha hd had hadD hdT hr hα).eq, mul_inv_cancel_right]
  have key : ∀ u v : ZMod 2, 0 = u + v → u = v := by decide
  have hinv : ∀ m ∈ nCore D a, ∀ b ∈ nCore D a,
      lam (m⁻¹ * b * m⁻¹⁻¹ * b⁻¹) = lam (m * b * m⁻¹ * b⁻¹) := by
    intro m hm b hb
    have := hFH.lam_mul_left hlam (Subgroup.inv_mem _ hm) hm hb
    rw [show m⁻¹ * m * b * (m⁻¹ * m)⁻¹ * b⁻¹ = 1 by group, FormHyp.lam_one hlam] at this
    exact key _ _ this
  have hrad : ∀ b ∈ comSub D a d, (∀ b' ∈ comSub D a d, lam (b * b' * b⁻¹ * b'⁻¹) = 0) →
      b ∈ rootGroup D a := by
    let Rad : Subgroup G :=
      { carrier := {b | b ∈ comSub D a d ∧ ∀ b' ∈ comSub D a d, lam (b * b' * b⁻¹ * b'⁻¹) = 0}
        mul_mem' := fun {b₁ b₂} h₁ h₂ => ⟨Subgroup.mul_mem _ h₁.1 h₂.1, fun b' hb' => by
          rw [hFH.lam_mul_left hlam (hBM h₁.1) (hBM h₂.1) (hBM hb'), h₁.2 b' hb', h₂.2 b' hb',
            add_zero]⟩
        one_mem' := ⟨Subgroup.one_mem _, fun b' _ => by
          rw [show (1 : G) * b' * 1⁻¹ * b'⁻¹ = 1 by group]
          exact FormHyp.lam_one hlam⟩
        inv_mem' := fun {b} h => ⟨Subgroup.inv_mem _ h.1, fun b' hb' => by
          rw [hinv b (hBM h.1) b' (hBM hb')]
          exact h.2 b' hb'⟩ }
    have hARad : rootGroup D a ≤ Rad := fun α hα => ⟨hAB hα, fun b' hb' => by
      rw [hFH.comm_eq_one_left hα (hBM hb'), FormHyp.lam_one hlam]⟩
    have hRadB : Rad ≤ comSub D a d := fun b hb => hb.1
    have hRadn : ∀ r ∈ lineGroup D a d, ∀ b ∈ Rad, r * b * r⁻¹ ∈ Rad := fun r hr b hb =>
      ⟨conj_mem_comSub C hr hb.1, fun b' hb' => by
        rw [hconj r hr b (hBM hb.1) b' (hBM hb')]
        exact hb.2 _ (hconjB r hr b' hb')⟩
    rcases eq_or_eq_of_le_comSub C K ha hd had hadD hdT hM hZ hARad hRadB hRadn with h | h
    · intro b hb hb'
      have : b ∈ Rad := ⟨hb, hb'⟩
      rwa [h] at this
    · exfalso
      have : δ ∈ Rad := by rw [h]; exact hδB
      exact hlam0 (this.2 l₀ hl₀B)
  refine le_antisymm hBM fun m hm => ?_
  obtain ⟨b, hb, hmb⟩ := hFH.exists_eq_of_radical hlam hrad hm
  have hpM : m * b⁻¹ ∈ nCore D a := Subgroup.mul_mem _ hm (Subgroup.inv_mem _ (hBM hb))
  have key' : ∀ u v : ZMod 2, u = v + u → v = 0 := by decide
  have hp : ∀ b' ∈ comSub D a d, lam (m * b⁻¹ * b' * (m * b⁻¹)⁻¹ * b'⁻¹) = 0 := by
    intro b' hb'
    have h1 := hFH.lam_mul_left hlam hpM (hBM hb) (hBM hb')
    rw [show m * b⁻¹ * b = m by group, hmb b' hb'] at h1
    exact key' _ _ h1
  have hpA : m * b⁻¹ ∈ rootGroup D a := by
    refine mem_rootGroup_of_comm_mem C K ha hd had hadD hdT hM hZ hpM fun r hr => ?_
    refine hrad _ (comm_mem_comSub hr hpM) fun b' hb' => ?_
    rw [hFH.lam_mul_left hlam (conj_mem_nCore_of_mem_lineGroup C hr hpM)
      (Subgroup.inv_mem _ hpM) (hBM hb'), hconj r hr _ hpM b' (hBM hb'),
      hinv _ hpM b' (hBM hb'), hp b' hb', hp _ (hconjB r hr b' hb'), add_zero]
  rw [show m = m * b⁻¹ * b by group]
  exact Subgroup.mul_mem _ (hAB hpA) hb

end Irr

end RootIrr

open RootIrr RootMany in
theorem thinGateIrrStep : ThinGateIrrStep := by
  intro G _ D q C K a ha d hd had hadD hdT hN hZ
  have := C.hyp.finite
  have hcard := card_nCore_eq C K ha hd had hadD hdT
  have hM : Nat.card (nCore D a) < q ^ 6 := by
    have hq := two_le_q C K ha
    rw [hcard]
    calc q ^ 3 * Nat.card ↥(nCore D a ⊓ nCore D d) < q ^ 3 * q ^ 3 :=
          Nat.mul_lt_mul_of_pos_left hN (pow_pos (by omega) 3)
      _ = q ^ 6 := by ring
  have hBM := comSub_eq C K ha hd had hadD hdT hM hZ
  obtain ⟨m, hm, hqm, -, f, hf, hker⟩ := exists_l2 C K ha hd had hadD hdT
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  obtain ⟨x, hx, c, hc, hxc⟩ := exists_conj_mul_inv_not_mem C ha hd had hadD hdT
    (three_le_ncard_rootLines C K ha)
  have h := (secHyp_nCore C K ha hd had hadD hdT).card_eq_of_irreducible f hf hker (by omega) hF
    (fun B' hAB hBM' hBn => by
      rw [← hBM] at hBM' ⊢
      exact eq_or_eq_of_le_comSub C K ha hd had hadD hdT hM hZ hAB hBM' hBn) hx hc hxc (by
      rw [hqm, K.card_rootGroup a ha]
      calc Nat.card (nCore D a) ^ 2 < (q ^ 6) ^ 2 := Nat.pow_lt_pow_left hM (by norm_num)
        _ = (q ^ 2) ^ 5 * q ^ 2 := by ring)
  rw [hqm, K.card_rootGroup a ha, hcard] at h
  have hq := two_le_q C K ha
  have h' : q ^ 3 * Nat.card ↥(nCore D a ⊓ nCore D d) = q ^ 3 * q ^ 2 := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 3) h'

end CFSG.Timmesfeld.Bridge
