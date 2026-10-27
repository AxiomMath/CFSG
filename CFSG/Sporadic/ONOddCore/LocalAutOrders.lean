module

public import CFSG.Sporadic.ONOddCore.LiftAut
public import CFSG.Sporadic.ONOddCore.QuotOuter

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ComponentClassification.OuterAutomorphisms

theorem resX_conj
    {r : RM} (hr : (r : Equiv.Perm (Fin 120)) ∈ onX) :
    resX (MulAut.conj r) = MulAut.conj (⟨r, hr⟩ : onX) := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [resX_apply]
  rfl

theorem resX_tauAut
    {k : ℕ} (hk : k < 12) :
    resX (tauAut k) = sigmaX (recK k).diag (recK k).field (recK k).graph := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [resX_apply]
  exact tauAut_X hk x

theorem tripleList_nodup : tripleList.Nodup := by decide

theorem recK_injective
    {k k' : ℕ} (hk : k < 12) (hk' : k' < 12)
    (h : ((recK k).diag, (recK k).field, (recK k).graph) =
      ((recK k').diag, (recK k').field, (recK k').graph)) : k = k' := by
  rw [recK_triple hk, recK_triple hk'] at h
  rw [List.getD_eq_getElem _ _ (by simpa [tripleList] using hk),
    List.getD_eq_getElem _ _ (by simpa [tripleList] using hk')] at h
  exact (tripleList_nodup.getElem_inj_iff).1 h

theorem tauAut_inj
    {k k' : ℕ} (hk : k < 12) (hk' : k' < 12) (h : tauAut k = tauAut k') :
    k = k' := by
  have hs := congrArg resX h
  rw [resX_tauAut hk, resX_tauAut hk'] at hs
  obtain ⟨hd, hf, hg⟩ := recK_bounds hk
  obtain ⟨hd', hf', hg'⟩ := recK_bounds hk'
  obtain ⟨e1, e2, e3⟩ := sigmaX_outer_injective hd hd' hf hf' hg hg' (congrArg _ hs)
  exact recK_injective hk hk' (by rw [e1, e2, e3])

abbrev AllLifts :
    Type := Σ k : Fin 12, liftSet k

@[expose] def lM
    (l : onX → onL) (x : onX) : onM := ⟨l x, onL_le_M (l x).2⟩

@[expose] def decompose
    (l : onX → onL) (p : onX × AllLifts) : MulAut onM :=
  MulAut.conj (lM l p.1) * (p.2.2 : MulAut onM)

theorem piR_lM
    {l : onX → onL} (hl : ∀ x, piM (lM l x) = x) (x : onX) :
    piR (lM l x) = ⟨x, onX_le_RM x.2⟩ := Subtype.ext (hl x)

theorem resX_descend_conj
    {l : onX → onL} (hl : ∀ x, piM (lM l x) = x) (x : onX) :
    resX (descendAut (MulAut.conj (lM l x))) = MulAut.conj x := by
  rw [descendAut_conj, piR_lM hl, resX_conj x.2]

theorem resX_descend_lift
    {k : Fin 12} (β : liftSet k) :
    resX (descendAut (β : MulAut onM)) =
      sigmaX (recK k).diag (recK k).field (recK k).graph := by
  rw [show descendAut (β : MulAut onM) = tauAut k from β.2, resX_tauAut k.2]

theorem decompose_bijective
    {l : onX → onL} (hl : ∀ x, piM (lM l x) = x) :
    Function.Bijective (decompose l) := by
  constructor
  · rintro ⟨x, k, β⟩ ⟨x', k', β'⟩ h
    have h1 := congrArg (fun α => resX (descendAut α)) h
    simp only [decompose, descendAut_mul, map_mul, resX_descend_conj hl, resX_descend_lift] at h1
    have h2 := congrArg (fun α : MulAut onX => (α : Outer onX)) h1
    have hc : ∀ y : onX, ((MulAut.conj y : MulAut onX) : Outer onX) = 1 := fun y =>
      (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨y, rfl⟩)
    simp only [QuotientGroup.mk_mul, hc, one_mul] at h2
    obtain ⟨hd, hf, hg⟩ := recK_bounds k.2
    obtain ⟨hd', hf', hg'⟩ := recK_bounds k'.2
    obtain ⟨e1, e2, e3⟩ := sigmaX_outer_injective hd hd' hf hf' hg hg' h2
    have hkk : k = k' := Fin.ext (recK_injective k.2 k'.2 (by rw [e1, e2, e3]))
    subst hkk
    rw [mul_left_inj] at h1
    have hxx : x = x' := conj_injective_X h1
    subst hxx
    rw [decompose, decompose, mul_right_inj] at h
    have hββ : β = β' := Subtype.ext h
    subst hββ
    rfl
  · intro α
    obtain ⟨d, hd, f, hf, g, hg, x, hx⟩ := exists_sigma (resX (descendAut α))
    obtain ⟨k, hk, rfl, rfl, rfl⟩ := exists_record hd hf hg
    set β := (MulAut.conj (lM l x))⁻¹ * α with hβ
    have hβk : β ∈ liftSet k := by
      apply resX_injective
      rw [hβ, descendAut_mul, descendAut_inv, map_mul, map_inv, resX_descend_conj hl, hx,
        inv_mul_cancel_left, resX_tauAut hk]
    refine ⟨(x, ⟨⟨k, hk⟩, ⟨β, hβk⟩⟩), ?_⟩
    simp only [decompose, hβ, mul_inv_cancel_left]

theorem exists_section :
    ∃ l : onX → onL, ∀ x, piM (lM l x) = x := by
  have h : ∀ x : onX, ∃ y : onL, piM ⟨y, onL_le_M y.2⟩ = x := by
    intro x
    have hx : (x : Equiv.Perm (Fin 120)) ∈ (onL.subgroupOf onM).map piM := by
      rw [map_L_piM]
      exact x.2
    obtain ⟨m, hm, hmx⟩ := hx
    exact ⟨⟨m, Subgroup.mem_subgroupOf.1 hm⟩, hmx⟩
  exact ⟨fun x => (h x).choose, fun x => (h x).choose_spec⟩

theorem card_allLifts :
    Nat.card AllLifts = 16 := by
  rw [Nat.card_sigma]
  have h : ∀ k : Fin 12, Nat.card (liftSet k) = (recK k).lifts.length := fun k => by
    rw [Nat.card_coe_set_eq, ncard_liftSet k.2]
  simp only [h]
  have hl : ∀ k : Fin 12, (recK k).lifts.length = [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0].getD k 0 :=
    fun k => recK_lifts_length k.2
  simp only [hl]
  decide

theorem card_mulAut_M :
    Nat.card (MulAut onM) = 322560 := by
  obtain ⟨l, hl⟩ := exists_section
  rw [← Nat.card_eq_of_bijective _ (decompose_bijective hl), Nat.card_prod, card_onX,
    card_allLifts]

theorem card_center_M :
    Nat.card (Subgroup.center onM) = 2 := by
  rw [← card_onM_centerIn, CFSG.centerIn_eq_map_center,
    Subgroup.card_map_of_injective onM.subtype_injective]

theorem conj_ker_eq_center (G : Type*) [Group G] :
    (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have hx := DFunLike.congr_fun h x
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * g = g * x * g⁻¹ * g := by rw [hx]
      _ = g * x := by group
  · intro h
    refine MulEquiv.ext fun x => ?_
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]
    group

theorem card_inner_M :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner onM) = 80640 := by
  have h := card_range_mul_ker (MulAut.conj : onM →* MulAut onM)
  rw [conj_ker_eq_center, card_center_M, card_onM] at h
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner]
  omega

theorem card_outer_M :
    Nat.card (Outer onM) = 4 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner onM)
  rw [card_mulAut_M, card_inner_M] at h
  have h' : Nat.card (Outer onM) * 80640 = 4 * 80640 := by
    rw [← h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

@[expose] def liftTriples : List (ℕ × ℕ × ℕ) := [(0, 0, 0), (0, 1, 1), (2, 0, 1), (2, 1, 0)]

theorem ncard_liftSet_triple
    {k : ℕ} (hk : k < 12) :
    (liftSet k).ncard = if ((recK k).diag, (recK k).field, (recK k).graph) ∈ liftTriples
      then 4 else 0 := by
  rw [ncard_liftSet hk, recK_lifts_length hk, recK_triple hk]
  interval_cases k <;> decide

theorem descend_iff
    {k : ℕ} (β : MulAut onM) :
    (∀ m, piR (β m) = tauAut k (piR m)) ↔ β ∈ liftSet k := by
  constructor
  · intro h
    refine MulEquiv.ext fun r => ?_
    obtain ⟨m, rfl⟩ := piR_surjective r
    rw [descendAut_piR, h]
  · intro h m
    rw [← descendAut_piR, show descendAut β = tauAut k from h]

theorem r3e_on_local_automorphism_and_outer_orders :
    (onQ.subgroupOf onM).Characteristic ∧
      (∀ k < 12, ∀ β : MulAut onM, (∀ m, piR (β m) = tauAut k (piR m)) ↔ β ∈ liftSet k) ∧
      (∀ k < 12, (liftSet k).ncard =
        if ((recK k).diag, (recK k).field, (recK k).graph) ∈ liftTriples then 4 else 0) ∧
      (∀ k < 12, liftSet k = {β : MulAut onM | ∃ e ∈ (recK k).lifts, ⇑β = liftFun e}) ∧
      (∀ k < 12, ∀ e ∈ (recK k).lifts,
        ∃ β ∈ liftSet k, ⇑β = liftFun e ∧ β qM = qM ^ e.power) ∧
      (∀ l : onX → onL, (∀ x, piM (lM l x) = x) → Function.Bijective (decompose l)) ∧
      Nat.card (MulAut onM) = 322560 ∧
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner onM) = 80640 ∧
      Nat.card (Outer onM) = 4 := by
  refine ⟨Q_characteristic, fun k _ β => descend_iff β, fun k hk => ncard_liftSet_triple hk,
    fun k hk => ?_, fun k hk e he => ⟨liftAut hk he, liftAut_mem hk he,
      liftAut_eq_liftFun hk he, liftAut_q hk he⟩, fun l hl => decompose_bijective hl,
    card_mulAut_M, card_inner_M, card_outer_M⟩
  ext β
  rw [mem_liftSet_iff hk]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, getD_mem hi default, liftAut_eq_liftFun hk _⟩
  · rintro ⟨e, he, hβ⟩
    obtain ⟨i, hi, rfl⟩ := mem_lifts_iff.1 he
    refine ⟨i, hi, MulEquiv.ext fun m => ?_⟩
    have := congrFun hβ m
    rw [← liftAut_eq_liftFun hk he] at this
    exact this

end CFSG.Sporadic.ONOddCore
