module

public import CFSG.Quasithin.H13.AS91Sec5ResFacts
public import Certificates.Certificate89022

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

theorem duad_eY_mem_coreMod {T : Finset (Fin 24)} (hT : Even T.card) :
    eY T ∈ G6.coreMod 24 := by
  rw [mem_coreMod_iff, sum_toAdd_eY]
  exact (ZMod.natCast_eq_zero_iff_even).2 hT

theorem duad_eY_symmDiff (S T : Finset (Fin 24)) : eY (symmDiff S T) = eY S * eY T := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_eY, Finset.mem_symmDiff]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]
  decide

theorem duad_setClass_mul (S T : Finset (Fin 24)) :
    setClass S * setClass T = setClass (symmDiff S T) := by
  unfold setClass
  rw [duad_eY_symmDiff, map_mul]

theorem duad_setClass_eq_iff {S T : Finset (Fin 24)} (hS : Even S.card) (hT : Even T.card) :
    setClass S = setClass T ↔ eY S * eY T ∈ golayC := by
  have hmem : eY S * eY T ∈ G6.coreMod 24 :=
    (G6.coreMod 24).mul_mem (duad_eY_mem_coreMod hS) (duad_eY_mem_coreMod hT)
  rw [← cocodeCoords.ker_iff _ hmem, map_mul]
  constructor
  · intro h
    change setClass S * setClass T = 1
    rw [h]
    exact W11_mul_self _
  · intro h
    have h1 : setClass S = (setClass T)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (W11_mul_self _)

theorem duad_eq_of_setClass_eq {S T : Finset (Fin 24)} (hS : Even S.card) (hT : Even T.card)
    (hlt : S.card + T.card < 8) (h : setClass S = setClass T) : S = T :=
  (eY_mul_eY_mem_golayC_iff S T hlt).1 ((duad_setClass_eq_iff hS hT).1 h)

theorem duad_setClass_eq_one_iff {S : Finset (Fin 24)} (hS : Even S.card) (h8 : S.card < 8) :
    setClass S = 1 ↔ S = ∅ := by
  rw [← eY_mem_golayC_iff S h8]
  exact cocodeCoords.ker_iff _ (duad_eY_mem_coreMod hS)

theorem duad_sextet_nonempty {U : Finset (Finset (Fin 24))} (hU : IsSextet U) : U.Nonempty := by
  rw [← Finset.card_pos, hU.1]
  norm_num

@[expose] def IsDuadClass (w : W11) : Prop := ∃ D : Finset (Fin 24), D.card = 2 ∧ setClass D = w

@[expose] def IsSextClass (w : W11) : Prop := ∃ U, IsSextet U ∧ sextClass U = w

theorem setClass_ne_one_of_card_two {D : Finset (Fin 24)} (hD : D.card = 2) : setClass D ≠ 1 := by
  intro h
  have h1 := (duad_setClass_eq_one_iff (by rw [hD]; decide) (by omega)).1 h
  rw [h1] at hD
  simp at hD

theorem setClass_injOn_duads {D D' : Finset (Fin 24)} (hD : D.card = 2) (hD' : D'.card = 2)
    (h : setClass D = setClass D') : D = D' :=
  duad_eq_of_setClass_eq (by rw [hD]; decide) (by rw [hD']; decide) (by omega) h

theorem not_isSextClass_of_isDuadClass {w : W11} (hw : IsDuadClass w) : ¬ IsSextClass w := by
  rintro ⟨U, hU, rfl⟩
  obtain ⟨D, hD, hDw⟩ := hw
  obtain ⟨T, hT⟩ := duad_sextet_nonempty hU
  rw [sextClass_eq hU hT] at hDw
  have hT4 := hU.2.1 T hT
  have hDT := duad_eq_of_setClass_eq (by rw [hD]; decide) (by rw [hT4]; decide) (by omega) hDw
  rw [hDT, hT4] at hD
  omega

section Cover


theorem duadCheck_true : Native.duadCheck () = true := Certificates.certificate89022

theorem duadCheck_parts : Native.duadCoverCheck () = true ∧ Native.duadPairOrbitCheck () = true ∧
    Native.duadGrpCheck Native.duadP1Gens 128 = true ∧
    Native.duadEaCheck Native.duadP1Gens 128 = true ∧
    Native.duadGrpCheck Native.duadP2Gens 128 = true ∧
    Native.duadEaCheck Native.duadP2Gens 128 = true ∧
    Native.duadGrpCheck Native.duadQ3Gens 9 = true ∧ Native.duadS2Check () = true ∧
    Native.duadSatCheck () = true := by
  have h := duadCheck_true
  simp only [Native.duadCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem duad_cover_spec : ∀ m < 2048, m ≠ 0 → m ∈ Native.duadMasks () ∨
    (Native.scTab (Native.clsTab (Native.sextList ())))[m]! = true := by
  have h := duadCheck_parts.1
  unfold Native.duadCoverCheck at h
  simp only [Native.allLt_iff, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem,
    decide_eq_true_eq] at h
  intro m hm hm0
  rcases h m hm with (h0 | h1) | h2
  · exact absurd h0 hm0
  · exact Or.inl h1
  · exact Or.inr h2

end Cover

theorem duad_maskFin (a b : Fin 24) :
    maskFin ((1 <<< (a : ℕ)) ||| (1 <<< (b : ℕ))) = {a, b} := by
  ext i
  simp only [mem_maskFin, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
    Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem duadMasks_spec {m : ℕ} (hm : m ∈ Native.duadMasks ()) :
    ∃ D : Finset (Fin 24), D.card = 2 ∧ setClass D = toW 11 m := by
  simp only [Native.duadMasks, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at hm
  obtain ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩ := hm
  refine ⟨{⟨i, hi⟩, ⟨j, hj⟩}, ?_, ?_⟩
  · rw [Finset.card_pair]
    intro h
    simp only [Fin.mk.injEq] at h
    omega
  · have h := duad_maskFin ⟨i, hi⟩ ⟨j, hj⟩
    simp only at h
    rw [← h, setClass_maskFin]
    exact congrArg (toW 11) (actM_eq_actM _ _).symm

section CoverSext


private theorem duad_clsTab_get {q : ℕ} (hq : q < (Native.sextList ()).size) :
    (Native.clsTab (Native.sextList ()))[q]! = clsMask q := by
  unfold Native.clsTab clsMask
  rw [getElem!_pos ((Native.sextList ()).map Native.clsOf) q (by simpa using hq),
    getElem!_pos (Native.sextList ()) q hq]
  simp

theorem duad_scTab_iff {m : ℕ} (hm : m < 2048) :
    (Native.scTab (Native.clsTab (Native.sextList ())))[m]! = true ↔
      ∃ q < 1771, clsMask q = m := by
  unfold Native.scTab
  rw [getElem!_pos (Array.map _ (Array.range 2048)) m (by simpa using hm)]
  simp only [Array.getElem_map, Array.getElem_range, List.contains_iff_mem, decide_eq_true_eq]
  have hsz : (Native.sextList ()).size = 1771 := clsDistinct_spec.1
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < 1771 := by simpa [Native.clsTab, hsz] using hj
    refine ⟨j, hj', ?_⟩
    rw [← duad_clsTab_get (hsz ▸ hj'), getElem!_pos (Native.clsTab (Native.sextList ())) j hj]
  · rintro ⟨q, hq, rfl⟩
    have hq' : q < (Native.clsTab (Native.sextList ())).size := by
      simpa [Native.clsTab, hsz] using hq
    refine ⟨q, hq', ?_⟩
    rw [← getElem!_pos (Native.clsTab (Native.sextList ())) q hq', duad_clsTab_get (hsz ▸ hq)]


theorem isDuadClass_or_isSextClass {w : W11} (hw : w ≠ 1) : IsDuadClass w ∨ IsSextClass w := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
  have hm' : m < 2048 := by simpa using hm
  have hm0 : m ≠ 0 := fun h => hw (by rw [h]; exact toW_zero 11)
  rcases duad_cover_spec m hm' hm0 with h | h
  · obtain ⟨D, hD, hDm⟩ := duadMasks_spec h
    exact Or.inl ⟨D, hD, hDm⟩
  · obtain ⟨q, hq, hqm⟩ := (duad_scTab_iff hm').1 h
    refine Or.inr ⟨sextFin q, isSextet_sextFin hq, ?_⟩
    rw [sextClass_sextFin hq, hqm]

theorem duad_isSextClass_of_card_four {T : Finset (Fin 24)} (hT : T.card = 4) :
    IsSextClass (setClass T) := by
  have hne : setClass T ≠ 1 := fun h => by
    have := (duad_setClass_eq_one_iff (by rw [hT]; decide) (by omega)).1 h
    rw [this] at hT
    simp at hT
  rcases isDuadClass_or_isSextClass hne with ⟨D, hD, hDT⟩ | h
  · exfalso
    have := duad_eq_of_setClass_eq (by rw [hD]; decide) (by rw [hT]; decide) (by omega) hDT
    rw [this, hT] at hD
    omega
  · exact h

end CoverSext

noncomputable local instance duadAction : MulAction ↥AutPerm W11 where
  smul σ w := rho11 AutPerm le_rfl σ w
  one_smul w := by
    show rho11 AutPerm le_rfl 1 w = w
    rw [map_one]
    rfl
  mul_smul σ τ w := by
    show rho11 AutPerm le_rfl (σ * τ) w = rho11 AutPerm le_rfl σ (rho11 AutPerm le_rfl τ w)
    rw [map_mul]
    rfl

theorem duad_smul_def (σ : ↥AutPerm) (w : W11) : σ • w = rho11 AutPerm le_rfl σ w := rfl

theorem duad_isDuadClass_rho_of {σ : S24} (hσ : σ ∈ M24g) {w : W11} (hw : IsDuadClass w) :
    IsDuadClass (rho11 AutPerm le_rfl ⟨σ, hσ⟩ w) := by
  obtain ⟨D, hD, rfl⟩ := hw
  exact ⟨σ • D, by rw [Finset.card_smul_finset, hD], setClass_smul hσ (by rw [hD]; decide)⟩

theorem isDuadClass_rho {σ : S24} (hσ : σ ∈ M24g) {w : W11} :
    IsDuadClass (rho11 AutPerm le_rfl ⟨σ, hσ⟩ w) ↔ IsDuadClass w := by
  refine ⟨fun h => ?_, duad_isDuadClass_rho_of hσ⟩
  have h2 := duad_isDuadClass_rho_of (M24g.inv_mem hσ) h
  have h1 : (⟨σ⁻¹, (M24g.inv_mem hσ : σ⁻¹ ∈ AutPerm)⟩ : ↥AutPerm) * ⟨σ, hσ⟩ = 1 :=
    Subtype.ext (inv_mul_cancel σ)
  have e : rho11 AutPerm le_rfl ⟨σ⁻¹, (M24g.inv_mem hσ : σ⁻¹ ∈ AutPerm)⟩
      (rho11 AutPerm le_rfl ⟨σ, hσ⟩ w) = w := by
    rw [← MulAut.mul_apply, ← map_mul, h1, map_one, MulAut.one_apply]
  rwa [e] at h2

section Trans


theorem duad_transitive {D D' : Finset (Fin 24)} (hD : D.card = 2) (hD' : D'.card = 2) :
    ∃ σ ∈ M24g, σ • D = D' := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hD
  obtain ⟨a', b', hab', rfl⟩ := Finset.card_eq_two.1 hD'
  obtain ⟨p, hp, hp0, hp1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hab
  obtain ⟨q, hq, hq0, hq1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a' b' hab'
  refine ⟨q * p⁻¹, M24g.mul_mem hq (M24g.inv_mem hp), ?_⟩
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton]
  have h1 : (q * p⁻¹) • a = a' := by
    rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, (Equiv.Perm.inv_eq_iff_eq).2 hp0.symm, hq0]
  have h2 : (q * p⁻¹) • b = b' := by
    rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, (Equiv.Perm.inv_eq_iff_eq).2 hp1.symm, hq1]
  rw [h1, h2]

theorem exists_stab01_smul (c : Fin 24) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ∃ σ ∈ M24g, σ • ({0, 1} : Finset (Fin 24)) = {0, 1} ∧ σ 2 = c := by
  have key : ∀ d : Fin 24, d ≠ 0 → d ≠ 1 → d ≠ c →
      ∃ σ ∈ M24g, σ • ({0, 1} : Finset (Fin 24)) = {0, 1} ∧ σ 2 = c := by
    intro d hd0 hd1 hdc
    obtain ⟨p, hp, h0, h1, h2, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_four 0 1 c d (by decide)
      (Ne.symm hc0) (Ne.symm hd0) (Ne.symm hc1) (Ne.symm hd1) (Ne.symm hdc)
    refine ⟨p, hp, ?_, h2⟩
    rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, Equiv.Perm.smul_def,
      Equiv.Perm.smul_def, h0, h1]
  by_cases h2 : c = 2
  · exact key 3 (by decide) (by decide) (by rw [h2]; decide)
  · exact key 2 (by decide) (by decide) (Ne.symm h2)

end Trans

theorem duad_dot24_eY_eY (X C : Finset (Fin 24)) :
    dot24 (eY X) (eY C) = ((X ∩ C).card : ZMod 2) := by
  rw [dot24_comm, dot24_eY]
  simp only [toAdd_eY]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]

theorem duad_card_inter_symmDiff_parity (A B C : Finset (Fin 24)) :
    ((symmDiff A B ∩ C).card : ZMod 2) = ((A ∩ C).card : ZMod 2) + ((B ∩ C).card : ZMod 2) := by
  rw [← duad_dot24_eY_eY, ← duad_dot24_eY_eY, ← duad_dot24_eY_eY, duad_eY_symmDiff, dot24_mul_left]

theorem duad_even_card_symmDiff {S T : Finset (Fin 24)} (hS : Even S.card) (hT : Even T.card) :
    Even (symmDiff S T).card := by
  have h : ((symmDiff S T).card : ZMod 2) = (S.card : ZMod 2) + (T.card : ZMod 2) := by
    rw [← sum_toAdd_eY, ← sum_toAdd_eY, ← sum_toAdd_eY, duad_eY_symmDiff]
    simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib]
  have h0 : (S.card : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff_even).2 hS
  have h1 : (T.card : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff_even).2 hT
  rw [h0, h1, add_zero] at h
  exact (ZMod.natCast_eq_zero_iff_even).1 h

theorem duad_symmDiff_subset_union (S T : Finset (Fin 24)) : symmDiff S T ⊆ S ∪ T := by
  intro x hx
  rw [Finset.mem_symmDiff] at hx
  rw [Finset.mem_union]
  tauto

theorem card_inter_of_isDuadClass_mul {D D' : Finset (Fin 24)} (hD : D.card = 2)
    (hD' : D'.card = 2) (hne : D ≠ D') (h : IsDuadClass (setClass D * setClass D')) :
    (D ∩ D').card = 1 := by
  obtain ⟨E, hE, hEe⟩ := h
  rw [duad_setClass_mul] at hEe
  have hlt : (D ∩ D').card < 2 := by
    by_contra hge
    have h1 : D ∩ D' = D := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have h2 : D ∩ D' = D' := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (h1.symm.trans h2)
  by_contra hne1
  have h0 : D ∩ D' = ∅ := Finset.card_eq_zero.1 (by omega)
  have hsd : symmDiff D D' = D ∪ D' := by
    ext x
    rw [Finset.mem_symmDiff, Finset.mem_union]
    have hx : x ∈ D → x ∈ D' → False := fun h1 h2 => by
      have : x ∈ D ∩ D' := Finset.mem_inter.2 ⟨h1, h2⟩
      rw [h0] at this
      simp at this
    tauto
  have hcard : (D ∪ D').card = 4 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.2 h0), hD, hD']
  have hEq := duad_eq_of_setClass_eq (by rw [hE]; decide) (by rw [hsd, hcard]; decide)
    (by rw [hsd, hcard, hE]; omega) hEe
  rw [hEq, hsd, hcard] at hE
  omega

theorem card_le_four_of_forall_isDuadClass (V : Subgroup W11)
    (hV : ∀ v ∈ V, v ≠ 1 → IsDuadClass v) : Nat.card V ≤ 4 := by
  classical
  by_contra hgt
  push Not at hgt
  have hsub : ∀ F : Finset W11, (∀ v ∈ V, v ∈ F) → Nat.card V ≤ F.card := by
    intro F hF
    calc Nat.card V = (V : Set W11).ncard := Nat.card_coe_set_eq _
      _ ≤ (F : Set W11).ncard := Set.ncard_le_ncard hF (Set.toFinite _)
      _ = F.card := Set.ncard_coe_finset F
  obtain ⟨v1, hv1, hv11⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 := hsub {1} fun v hv => by simpa using hcon v hv
    rw [Finset.card_singleton] at h1
    omega
  obtain ⟨v2, hv2, hv21, hv2v1⟩ : ∃ v ∈ V, v ≠ 1 ∧ v ≠ v1 := by
    by_contra hcon
    push Not at hcon
    have := hsub {1, v1} fun v hv => by
      by_cases h1 : v = 1
      · simp [h1]
      · simp [hcon v hv h1]
    have h2 := Finset.card_le_two (a := (1 : W11)) (b := v1)
    omega
  obtain ⟨v3, hv3, hv31, hv3v1, hv3v2, hv3u⟩ :
      ∃ v ∈ V, v ≠ 1 ∧ v ≠ v1 ∧ v ≠ v2 ∧ v ≠ v1 * v2 := by
    by_contra hcon
    push Not at hcon
    have := hsub {1, v1, v2, v1 * v2} fun v hv => by
      by_cases h1 : v = 1
      · simp [h1]
      by_cases h2 : v = v1
      · simp [h2]
      by_cases h3 : v = v2
      · simp [h3]
      · simp [hcon v hv h1 h2 h3]
    have h2 := Finset.card_le_four (a := (1 : W11)) (b := v1) (c := v2) (d := v1 * v2)
    omega
  obtain ⟨D1, hD1, rfl⟩ := hV v1 hv1 hv11
  obtain ⟨D2, hD2, rfl⟩ := hV v2 hv2 hv21
  obtain ⟨D3, hD3, rfl⟩ := hV v3 hv3 hv31
  have hne12 : D1 ≠ D2 := fun h => hv2v1 (by rw [h])
  have hne13 : D1 ≠ D3 := fun h => hv3v1 (by rw [h])
  have hne23 : D2 ≠ D3 := fun h => hv3v2 (by rw [h])
  have hu1 : setClass D1 * setClass D2 ≠ 1 := by
    intro h
    apply hv2v1
    have h1 : setClass D2 = (setClass D1)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (W11_mul_self _)
  obtain ⟨D12, hD12, hD12e⟩ := hV _ (V.mul_mem hv1 hv2) hu1
  have hi12 : (D1 ∩ D2).card = 1 :=
    card_inter_of_isDuadClass_mul hD1 hD2 hne12 ⟨D12, hD12, hD12e⟩
  have hi13 : (D1 ∩ D3).card = 1 := card_inter_of_isDuadClass_mul hD1 hD3 hne13
    (hV _ (V.mul_mem hv1 hv3) (fun h => hv3v1 (by
      have h1 : setClass D3 = (setClass D1)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h1]
      exact inv_eq_of_mul_eq_one_right (W11_mul_self _))))
  have hi23 : (D2 ∩ D3).card = 1 := card_inter_of_isDuadClass_mul hD2 hD3 hne23
    (hV _ (V.mul_mem hv2 hv3) (fun h => hv3v2 (by
      have h1 : setClass D3 = (setClass D2)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h1]
      exact inv_eq_of_mul_eq_one_right (W11_mul_self _))))
  have hD12e' : setClass D12 = setClass (symmDiff D1 D2) := by rw [hD12e, duad_setClass_mul]
  have hsd : symmDiff D1 D2 = D12 := by
    refine (duad_eq_of_setClass_eq (S := D12) (T := symmDiff D1 D2) (by rw [hD12]; decide)
      (duad_even_card_symmDiff (by rw [hD1]; decide) (by rw [hD2]; decide))
      (by
        have h1 := Finset.card_le_card (duad_symmDiff_subset_union D1 D2)
        have h2 := Finset.card_union_le D1 D2
        omega) hD12e').symm
  have hu12 : setClass D12 ∈ V := hD12e ▸ V.mul_mem hv1 hv2
  have hu3 : setClass D12 * setClass D3 ≠ 1 := by
    intro h
    apply hv3u
    have h1 : setClass D3 = (setClass D12)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, inv_eq_of_mul_eq_one_right (W11_mul_self _), hD12e]
  have hne123 : D12 ≠ D3 := fun h => hv3u (by rw [← hD12e, h])
  have hi123 : (D12 ∩ D3).card = 1 :=
    card_inter_of_isDuadClass_mul hD12 hD3 hne123 (hV _ (V.mul_mem hu12 hv3) hu3)
  have hpar := duad_card_inter_symmDiff_parity D1 D2 D3
  rw [hsd, hi123, hi13, hi23] at hpar
  revert hpar
  decide

@[expose] def duadPpPerm0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 7, 16, 5, 9, 19, 10, 8, 13, 21, 3, 4, 12, 14, 18, 15, 2, 11, 20, 23, 17, 6, 22]
  invFun := ![0, 1, 17, 11, 12, 4, 22, 2, 8, 5, 7, 18, 13, 9, 14, 16, 3, 21, 15, 6, 19, 10, 23, 20]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadPpPerm1 : Equiv.Perm (Fin 24) where
  toFun := ![1, 0, 7, 13, 23, 14, 5, 20, 22, 9, 2, 18, 10, 12, 11, 6, 19, 15, 17, 4, 21, 16, 3, 8]
  invFun := ![1, 0, 10, 22, 19, 6, 15, 2, 23, 9, 12, 14, 13, 3, 5, 17, 21, 18, 11, 16, 7, 20, 8, 4]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadPpPerm : Fin 2 → Equiv.Perm (Fin 24) := ![duadPpPerm0, duadPpPerm1]

theorem repT_duadPpPerm (j : Fin 2) : RepT (Native.duadPpGens.getD j #[]) (duadPpPerm j) := by
  revert j
  unfold RepT
  decide +kernel

private theorem duadPpPerm_basis :
    ∀ (j : Fin 2) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(duadPpPerm j) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem duadPpPerm_basis' :
    ∀ (j : Fin 2) (i : Fin 12),
      CFSG.Monster.Code.B i ∘ ⇑(duadPpPerm j)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem duadPpPerm_mem (j : Fin 2) : duadPpPerm j ∈ M24g :=
  mem_AutPerm_of_basis (duadPpPerm_basis j) (duadPpPerm_basis' j)

@[expose] def duadP1Perm0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadP1Perm1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 18, 19, 16, 17, 12, 15, 13, 14, 11, 9, 8, 10, 7, 6, 5, 4, 21, 20, 23, 22]
  invFun := ![0, 1, 2, 3, 19, 18, 17, 16, 14, 13, 15, 12, 8, 10, 11, 9, 6, 7, 4, 5, 21, 20, 23, 22]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadP1Perm2 : Equiv.Perm (Fin 24) where
  toFun := ![1, 0, 2, 3, 4, 6, 5, 7, 8, 11, 10, 9, 19, 16, 17, 18, 13, 14, 15, 12, 22, 21, 20, 23]
  invFun := ![1, 0, 2, 3, 4, 6, 5, 7, 8, 11, 10, 9, 19, 16, 17, 18, 13, 14, 15, 12, 22, 21, 20, 23]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadP1Perm : Fin 3 → Equiv.Perm (Fin 24) := ![duadP1Perm0, duadP1Perm1, duadP1Perm2]

theorem repT_duadP1Perm (j : Fin 3) : RepT (Native.duadP1Gens.getD j #[]) (duadP1Perm j) := by
  revert j
  unfold RepT
  decide +kernel

private theorem duadP1Perm_basis :
    ∀ (j : Fin 3) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(duadP1Perm j) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem duadP1Perm_basis' :
    ∀ (j : Fin 3) (i : Fin 12),
      CFSG.Monster.Code.B i ∘ ⇑(duadP1Perm j)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem duadP1Perm_mem (j : Fin 3) : duadP1Perm j ∈ M24g :=
  mem_AutPerm_of_basis (duadP1Perm_basis j) (duadP1Perm_basis' j)

@[expose] def duadP2Perm0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 18, 19, 16, 17, 22, 23, 20, 21, 10, 11, 8, 9, 14, 15, 12, 13]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 18, 19, 16, 17, 22, 23, 20, 21, 10, 11, 8, 9, 14, 15, 12, 13]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadP2Perm1 : Equiv.Perm (Fin 24) where
  toFun := ![1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10, 13, 12, 14, 15, 22, 23, 21, 20, 19, 18, 16, 17]
  invFun := ![1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10, 13, 12, 14, 15, 22, 23, 21, 20, 19, 18, 16, 17]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadP2Perm2 : Equiv.Perm (Fin 24) where
  toFun := ![1, 0, 3, 2, 7, 6, 5, 4, 8, 9, 10, 11, 14, 15, 12, 13, 18, 19, 16, 17, 20, 21, 22, 23]
  invFun := ![1, 0, 3, 2, 7, 6, 5, 4, 8, 9, 10, 11, 14, 15, 12, 13, 18, 19, 16, 17, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadP2Perm : Fin 3 → Equiv.Perm (Fin 24) := ![duadP2Perm0, duadP2Perm1, duadP2Perm2]

theorem repT_duadP2Perm (j : Fin 3) : RepT (Native.duadP2Gens.getD j #[]) (duadP2Perm j) := by
  revert j
  unfold RepT
  decide +kernel

private theorem duadP2Perm_basis :
    ∀ (j : Fin 3) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(duadP2Perm j) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem duadP2Perm_basis' :
    ∀ (j : Fin 3) (i : Fin 12),
      CFSG.Monster.Code.B i ∘ ⇑(duadP2Perm j)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem duadP2Perm_mem (j : Fin 3) : duadP2Perm j ∈ M24g :=
  mem_AutPerm_of_basis (duadP2Perm_basis j) (duadP2Perm_basis' j)

@[expose] def duadQ3Perm0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 4, 5, 3, 6, 7, 8, 15, 18, 21, 19, 20, 9, 14, 10, 13, 16, 23, 17, 22, 11, 12]
  invFun := ![0, 1, 2, 5, 3, 4, 6, 7, 8, 14, 16, 22, 23, 17, 15, 9, 18, 20, 10, 12, 13, 11, 21, 19]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadQ3Perm1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 6, 4, 5, 3, 7, 2, 8, 19, 16, 11, 20, 15, 12, 23, 18, 9, 10, 17, 14, 21, 22, 13]
  invFun := ![0, 1, 7, 5, 3, 4, 2, 6, 8, 17, 18, 11, 14, 23, 20, 13, 10, 19, 16, 9, 12, 21, 22, 15]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadQ3Perm : Fin 2 → Equiv.Perm (Fin 24) := ![duadQ3Perm0, duadQ3Perm1]

theorem repT_duadQ3Perm (j : Fin 2) : RepT (Native.duadQ3Gens.getD j #[]) (duadQ3Perm j) := by
  revert j
  unfold RepT
  decide +kernel

private theorem duadQ3Perm_basis :
    ∀ (j : Fin 2) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(duadQ3Perm j) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem duadQ3Perm_basis' :
    ∀ (j : Fin 2) (i : Fin 12),
      CFSG.Monster.Code.B i ∘ ⇑(duadQ3Perm j)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem duadQ3Perm_mem (j : Fin 2) : duadQ3Perm j ∈ M24g :=
  mem_AutPerm_of_basis (duadQ3Perm_basis j) (duadQ3Perm_basis' j)

@[expose] def duadXPerm0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 17, 14, 21, 10, 7, 23, 15, 5, 9, 19, 16, 3, 18, 22, 4, 11, 12, 13, 6, 20, 8]
  invFun := ![0, 1, 2, 14, 17, 10, 21, 7, 23, 11, 6, 18, 19, 20, 4, 9, 13, 3, 15, 12, 22, 5, 16, 8]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadXPerm1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 13, 22, 18, 9, 7, 19, 5, 11, 21, 23, 4, 16, 10, 17, 20, 6, 8, 14, 15, 3, 12]
  invFun := ![0, 1, 2, 22, 13, 9, 18, 7, 19, 6, 15, 10, 23, 3, 20, 21, 14, 16, 5, 8, 17, 11, 4, 12]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadXPerm2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 20, 16, 15, 11, 7, 12, 10, 18, 5, 8, 17, 13, 6, 3, 22, 21, 23, 4, 9, 14, 19]
  invFun := ![0, 1, 2, 16, 20, 11, 15, 7, 12, 21, 9, 6, 8, 14, 22, 5, 4, 13, 10, 23, 3, 18, 17, 19]
  left_inv := by decide
  right_inv := by decide

@[expose] def duadXPerm : Fin 3 → Equiv.Perm (Fin 24) := ![duadXPerm0, duadXPerm1, duadXPerm2]

theorem repT_duadXPerm (j : Fin 3) : RepT (Native.duadXWit.getD j #[]) (duadXPerm j) := by
  revert j
  unfold RepT
  decide +kernel

private theorem duadXPerm_basis :
    ∀ (j : Fin 3) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(duadXPerm j) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem duadXPerm_basis' :
    ∀ (j : Fin 3) (i : Fin 12),
      CFSG.Monster.Code.B i ∘ ⇑(duadXPerm j)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem duadXPerm_mem (j : Fin 3) : duadXPerm j ∈ M24g :=
  mem_AutPerm_of_basis (duadXPerm_basis j) (duadXPerm_basis' j)

section Tables

theorem repT_duadComp {a b : Array ℕ} {σ τ : S24} (ha : RepT a σ) (hb : RepT b τ) :
    RepT (Native.duadComp a b) (σ * τ) := by
  intro i
  have h1 : (Native.duadComp a b)[i.val]! = a[b[i.val]!]! := by
    unfold Native.duadComp
    rw [getElem!_pos ((Array.range 24).map fun i => a[b[i]!]!) i.val (by simp [i.2])]
    simp
  rw [h1, hb i, Equiv.Perm.mul_apply]
  exact ha (τ i)

theorem repT_duadId : RepT (Native.duadId ()) 1 := by
  intro i
  unfold Native.duadId
  rw [getElem!_pos (Array.range 24) i.val (by simp [i.2])]
  simp

theorem size_duadComp (a b : Array ℕ) : (Native.duadComp a b).size = 24 := by
  simp [Native.duadComp]

theorem size_duadId : (Native.duadId ()).size = 24 := by
  simp [Native.duadId]

theorem duad_repT_unique {a : Array ℕ} {σ τ : S24} (h1 : RepT a σ) (h2 : RepT a τ) : σ = τ :=
  Equiv.ext fun i => Fin.ext ((h1 i).symm.trans (h2 i))

theorem duad_arr_eq_of_repT {a b : Array ℕ} (ha : a.size = 24) (hb : b.size = 24) {σ : S24}
    (h1 : RepT a σ) (h2 : RepT b σ) : a = b := by
  apply Array.ext (ha.trans hb.symm)
  intro i hi1 hi2
  have e1 := h1 ⟨i, by omega⟩
  have e2 := h2 ⟨i, by omega⟩
  simp only at e1 e2
  rw [getElem!_pos a i hi1] at e1
  rw [getElem!_pos b i hi2] at e2
  rw [e1, e2]

@[expose] def duadGrpL (gens : List (Array ℕ)) (n : ℕ) : Array (Array ℕ) :=
  (Native.duadGrpData gens n).1

variable {m : ℕ} {gens : List (Array ℕ)} {gp : Fin m → S24}

theorem duad_exists_repT_of_tree (hm : gens.length = m)
    (hrep : ∀ j : Fin m, RepT (gens.getD j #[]) (gp j)) {valid : Array ℕ → Bool}
    {r : Array (Array ℕ) × Array ℕ × Array ℕ}
    (h : Native.treeValid valid (gens.map fun g t => Native.duadComp g t) (Native.duadId ())
      r = true) :
    ∀ j < r.1.size, ∃ σ ∈ Subgroup.closure (Set.range gp), RepT r.1[j]! σ := by
  obtain ⟨-, h0, hall⟩ := treeValid_get h
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases (hall j hj).2 with rfl | ⟨hpar, hgen, hstp⟩
    · exact ⟨1, Subgroup.one_mem _, by rw [h0]; exact repT_duadId⟩
    · obtain ⟨σ, hσ, hσr⟩ := ih r.2.1[j]! hpar (lt_trans hpar hj)
      have hgm : r.2.2[j]! < m := by simpa [hm] using hgen
      refine ⟨gp ⟨r.2.2[j]!, hgm⟩ * σ,
        Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, rfl⟩) hσ, ?_⟩
      rw [← hstp]
      have e := getD_map_of_lt (fun g t => Native.duadComp g t) gens #[] id
        (j := r.2.2[j]!) (by simpa using hgen)
      rw [e]
      exact repT_duadComp (hrep ⟨r.2.2[j]!, hgm⟩) hσr

theorem duadGrpCheck_parts {n : ℕ} (h : Native.duadGrpCheck gens n = true) :
    Native.treeValid Native.duadValidTab (gens.map fun g t => Native.duadComp g t)
        (Native.duadId ()) (Native.duadGrpData gens n) = true ∧
      (duadGrpL gens n).size = n ∧ (duadGrpL gens n).toList.Nodup ∧
      (∀ g ∈ gens, g ∈ duadGrpL gens n) ∧
      (∀ i < n, ∀ j < n,
        Native.duadComp (duadGrpL gens n)[i]! (duadGrpL gens n)[j]! ∈ duadGrpL gens n) ∧
      (∀ i < n, ∃ t ∈ duadGrpL gens n,
        Native.duadComp (duadGrpL gens n)[i]! t = Native.duadId ()) := by
  unfold Native.duadGrpCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Native.allLt_iff, Array.contains_iff_mem, Array.any_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro i hi
  obtain ⟨t, ht, ht2⟩ := h6 i hi
  exact ⟨t, ht, ht2⟩

variable {n : ℕ}

theorem duadGrp_size24 (h : Native.duadGrpCheck gens n = true) :
    ∀ i < n, (duadGrpL gens n)[i]!.size = 24 := by
  obtain ⟨ht, hsz, -⟩ := duadGrpCheck_parts h
  obtain ⟨-, -, hall⟩ := treeValid_get ht
  intro i hi
  have hi' : i < (Native.duadGrpData gens n).1.size := by
    show i < (duadGrpL gens n).size
    rw [hsz]
    exact hi
  have h1 := (hall i hi').1
  simp only [Native.duadValidTab, beq_iff_eq] at h1
  exact h1

theorem duadGrp_realize (hm : gens.length = m) (hrep : ∀ j : Fin m, RepT (gens.getD j #[]) (gp j))
    (h : Native.duadGrpCheck gens n = true) :
    ∀ i < n, ∃ σ ∈ Subgroup.closure (Set.range gp), RepT (duadGrpL gens n)[i]! σ := by
  obtain ⟨ht, hsz, -⟩ := duadGrpCheck_parts h
  intro i hi
  exact duad_exists_repT_of_tree hm hrep ht i (by
    show i < (duadGrpL gens n).size
    rw [hsz]
    exact hi)

theorem duadGrp_closure (hm : gens.length = m) (hrep : ∀ j : Fin m, RepT (gens.getD j #[]) (gp j))
    (h : Native.duadGrpCheck gens n = true) :
    ∀ σ ∈ Subgroup.closure (Set.range gp), ∃ i < n, RepT (duadGrpL gens n)[i]! σ := by
  obtain ⟨ht, hsz, hnd, hg, hmul, hinv⟩ := duadGrpCheck_parts h
  have hreal := duadGrp_realize hm hrep h
  obtain ⟨hpos, h0, -⟩ := treeValid_get ht
  have h0' : (duadGrpL gens n)[0]! = Native.duadId () := h0
  have hn : 0 < n := by
    have : 0 < (duadGrpL gens n).size := hpos
    rw [hsz] at this
    exact this
  have hmem : ∀ t ∈ duadGrpL gens n, ∃ i < n, (duadGrpL gens n)[i]! = t := by
    intro t ht'
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ht'
    exact ⟨i, by rw [← hsz]; exact hi, (getElem!_pos (duadGrpL gens n) i hi)⟩
  intro σ hσ
  refine Subgroup.closure_induction (p := fun x _ => ∃ i < n, RepT (duadGrpL gens n)[i]! x) ?_ ?_ ?_
    ?_ hσ
  · rintro _ ⟨j, rfl⟩
    have hj' : (j : ℕ) < gens.length := hm ▸ j.2
    have hjm : gens.getD j #[] ∈ gens := by
      rw [List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem hj'
    obtain ⟨i, hi, he⟩ := hmem _ (hg _ hjm)
    exact ⟨i, hi, by rw [he]; exact hrep j⟩
  · exact ⟨0, hn, by rw [h0']; exact repT_duadId⟩
  · rintro x y - - ⟨i, hi, hx⟩ ⟨j, hj, hy⟩
    obtain ⟨k, hk, he⟩ := hmem _ (hmul i hi j hj)
    exact ⟨k, hk, by rw [he]; exact repT_duadComp hx hy⟩
  · rintro x - ⟨i, hi, hx⟩
    obtain ⟨t, ht', hit⟩ := hinv i hi
    obtain ⟨k, hk, he⟩ := hmem t ht'
    obtain ⟨τ, -, hτ⟩ := hreal k hk
    refine ⟨k, hk, ?_⟩
    have h1 : RepT (Native.duadComp (duadGrpL gens n)[i]! (duadGrpL gens n)[k]!) (x * τ) :=
      repT_duadComp hx hτ
    rw [he, hit] at h1
    have h2 : x * τ = 1 := duad_repT_unique h1 repT_duadId
    have h3 : τ = x⁻¹ := eq_inv_of_mul_eq_one_right h2
    rw [← h3]
    exact hτ

theorem duadGrp_card (hm : gens.length = m) (hrep : ∀ j : Fin m, RepT (gens.getD j #[]) (gp j))
    (h : Native.duadGrpCheck gens n = true) :
    Nat.card (Subgroup.closure (Set.range gp)) = n := by
  classical
  obtain ⟨ht, hsz, hnd, -⟩ := duadGrpCheck_parts h
  have hsz24 := duadGrp_size24 h
  have hreal := duadGrp_realize hm hrep h
  have hcl := duadGrp_closure hm hrep h
  apply le_antisymm
  · let idx : Subgroup.closure (Set.range gp) → Fin n := fun σ =>
      ⟨(hcl σ.1 σ.2).choose, (hcl σ.1 σ.2).choose_spec.1⟩
    have hinj : Function.Injective idx := by
      intro σ τ hστ
      have e1 := (hcl σ.1 σ.2).choose_spec.2
      have e2 := (hcl τ.1 τ.2).choose_spec.2
      have : (hcl σ.1 σ.2).choose = (hcl τ.1 τ.2).choose := congrArg Fin.val hστ
      rw [this] at e1
      exact Subtype.ext (duad_repT_unique e1 e2)
    simpa using Nat.card_le_card_of_injective idx hinj
  · let el : Fin n → Subgroup.closure (Set.range gp) := fun i =>
      ⟨(hreal i.1 i.2).choose, (hreal i.1 i.2).choose_spec.1⟩
    have hinj : Function.Injective el := by
      intro i j hij
      have e1 := (hreal i.1 i.2).choose_spec.2
      have e2 := (hreal j.1 j.2).choose_spec.2
      have : (hreal i.1 i.2).choose = (hreal j.1 j.2).choose := congrArg Subtype.val hij
      rw [← this] at e2
      have h3 := duad_arr_eq_of_repT (hsz24 i.1 i.2) (hsz24 j.1 j.2) e1 e2
      have hi : i.1 < (duadGrpL gens n).size := by rw [hsz]; exact i.2
      have hj : j.1 < (duadGrpL gens n).size := by rw [hsz]; exact j.2
      rw [getElem!_pos _ i.1 hi, getElem!_pos _ j.1 hj] at h3
      have h4 : (duadGrpL gens n).toList[i.1]'(by simpa using hi) =
          (duadGrpL gens n).toList[j.1]'(by simpa using hj) := by simpa using h3
      exact Fin.ext ((hnd.getElem_inj_iff).1 h4)
    simpa using Nat.card_le_card_of_injective el hinj

theorem duad_isPGroup_two_of_sq {H : Type*} [Group H] {K : Subgroup H} (hK : ∀ a ∈ K, a * a = 1) :
    IsPGroup 2 K := by
  intro a
  exact ⟨1, Subtype.ext (by simpa [pow_two] using hK a a.2)⟩

theorem duad_mul_comm_of_sq {H : Type*} [Group H] {K : Subgroup H} (h : ∀ x ∈ K, x * x = 1)
    {x y : H}
    (hx : x ∈ K) (hy : y ∈ K) : x * y = y * x := by
  have hxy := h (x * y) (K.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

theorem mem_duadInvs {L : Array (Array ℕ)} {n i : ℕ} :
    i ∈ Native.duadInvs L n ↔ i < n ∧ Native.duadComp L[i]! L[i]! = Native.duadId () := by
  simp [Native.duadInvs]

theorem mem_duadCommWith {L : Array (Array ℕ)} {invs : List ℕ} {i j : ℕ} :
    j ∈ Native.duadCommWith L invs i ↔
      j ∈ invs ∧ Native.duadComp L[i]! L[j]! = Native.duadComp L[j]! L[i]! := by
  simp [Native.duadCommWith]

theorem mem_duadBad {L : Array (Array ℕ)} {n i : ℕ} :
    i ∈ Native.duadBad L n ↔ i ∈ Native.duadInvs L n ∧
      32 ≤ (Native.duadCommWith L (Native.duadInvs L n) i).length := by
  simp [Native.duadBad]

theorem duadGrp_ea (hm : gens.length = m) (hrep : ∀ j : Fin m, RepT (gens.getD j #[]) (gp j))
    (h : Native.duadGrpCheck gens n = true) (he : Native.duadEaCheck gens n = true)
    {K : Subgroup S24} (hK : K ≤ Subgroup.closure (Set.range gp)) (hK2 : ∀ b ∈ K, b * b = 1) :
    Nat.card K ≤ 16 := by
  classical
  have hcl := duadGrp_closure hm hrep h
  have hsz24 := duadGrp_size24 h
  have hbad : (Native.duadBad (duadGrpL gens n) n).length < 32 := by
    unfold Native.duadEaCheck at he
    simp only [decide_eq_true_eq] at he
    exact he
  haveI : Fintype K := Fintype.ofFinite K
  have h32 : Nat.card K < 32 := by
    by_contra h32
    push Not at h32
    let idx : K → ℕ := fun x => (hcl x.1 (hK x.2)).choose
    have hlt : ∀ x : K, idx x < n := fun x => (hcl x.1 (hK x.2)).choose_spec.1
    have hrp : ∀ x : K, RepT (duadGrpL gens n)[idx x]! x.1 := fun x =>
      (hcl x.1 (hK x.2)).choose_spec.2
    have hinj : Function.Injective idx := by
      intro x y hxy
      have e1 := hrp x
      have e2 := hrp y
      rw [hxy] at e1
      exact Subtype.ext (duad_repT_unique e1 e2)
    have hinv : ∀ x : K, idx x ∈ Native.duadInvs (duadGrpL gens n) n := by
      intro x
      rw [mem_duadInvs]
      refine ⟨hlt x, ?_⟩
      have h1 := repT_duadComp (hrp x) (hrp x)
      rw [hK2 x.1 x.2] at h1
      exact duad_arr_eq_of_repT (size_duadComp _ _) size_duadId h1 repT_duadId
    have hcomm : ∀ x y : K, Native.duadComp (duadGrpL gens n)[idx x]! (duadGrpL gens n)[idx y]! =
        Native.duadComp (duadGrpL gens n)[idx y]! (duadGrpL gens n)[idx x]! := by
      intro x y
      have h1 := repT_duadComp (hrp x) (hrp y)
      have h2 := repT_duadComp (hrp y) (hrp x)
      rw [duad_mul_comm_of_sq hK2 y.2 x.2] at h2
      exact duad_arr_eq_of_repT (size_duadComp _ _) (size_duadComp _ _) h1 h2
    have hJ : (Finset.univ.image idx).card = Nat.card K := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
    have hge : ∀ x : K, 32 ≤ (Native.duadCommWith (duadGrpL gens n)
        (Native.duadInvs (duadGrpL gens n) n) (idx x)).length := by
      intro x
      have hsub : Finset.univ.image idx ⊆ (Native.duadCommWith (duadGrpL gens n)
          (Native.duadInvs (duadGrpL gens n) n) (idx x)).toFinset := by
        intro j hj
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hj
        rw [List.mem_toFinset, mem_duadCommWith]
        exact ⟨hinv y, hcomm x y⟩
      calc 32 ≤ Nat.card K := h32
        _ = (Finset.univ.image idx).card := hJ.symm
        _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := List.toFinset_card_le _
    have hsub2 : Finset.univ.image idx ⊆ (Native.duadBad (duadGrpL gens n) n).toFinset := by
      intro j hj
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hj
      rw [List.mem_toFinset, mem_duadBad]
      exact ⟨hinv x, hge x⟩
    have h3 := Finset.card_le_card hsub2
    have h4 := List.toFinset_card_le (Native.duadBad (duadGrpL gens n) n)
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (G := K)).1 (duad_isPGroup_two_of_sq (K := K) hK2)
  rw [hk] at h32 ⊢
  have hk5 : k < 5 := by
    by_contra hk5
    push Not at hk5
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hk5
    omega
  calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 16 := by norm_num

theorem duad_card_le_sixteen_of_sylow {G : Type*} [Group G] [Finite G] {m : ℕ} (hm : Odd m)
    (hG : Nat.card G = 2 ^ 7 * m) (S0 : Subgroup G) (hS0 : Nat.card S0 = 2 ^ 7)
    (hq : ∀ K : Subgroup G, K ≤ S0 → (∀ b ∈ K, b * b = 1) → Nat.card K ≤ 16)
    (A : Subgroup G) (hA : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS0p : IsPGroup 2 S0 := IsPGroup.of_card hS0
  have hidx : S0.index = m := by
    have h := S0.card_mul_index
    rw [hS0, hG] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hnd : ¬ 2 ∣ S0.index := by
    rw [hidx]
    exact hm.not_two_dvd_nat
  let T : Sylow 2 G := hS0p.toSylow hnd
  have hT : (T : Subgroup G) = S0 := IsPGroup.toSylow_coe hS0p hnd
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (duad_isPGroup_two_of_sq hA)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T Q
  have hmem : ∀ x ∈ A, g⁻¹ * x * g ∈ S0 := by
    intro x hx
    have h1 : x ∈ (Q : Subgroup G) := hQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, hT] at h1
    exact h1
  have hconj : ∀ x : G, (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := fun x => by
    simp [MulAut.conj_apply]
  have hB : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ S0 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconj]
    exact hmem x hx
  have hBsq : ∀ b ∈ A.map (MulAut.conj g⁻¹).toMonoidHom, b * b = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconj]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hA x hx]; group
  have hc : Nat.card ↥(A.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card ↥A :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [← hc]
  exact hq _ hB hBsq

theorem duad_card_le_sixteen_of_sylow_sub {S P : Subgroup S24} {m : ℕ} (hm : Odd m)
    (hS : Nat.card S = 2 ^ 7 * m) (hP : P ≤ S) (hPc : Nat.card P = 2 ^ 7)
    (hq : ∀ K : Subgroup S24, K ≤ P → (∀ b ∈ K, b * b = 1) → Nat.card K ≤ 16)
    (B : Subgroup S24) (hB : B ≤ S) (hB2 : ∀ b ∈ B, b * b = 1) : Nat.card B ≤ 16 := by
  have hS0 : Nat.card (P.subgroupOf S) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv, hPc]
  have hA : Nat.card (B.subgroupOf S) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  rw [← hA]
  refine duad_card_le_sixteen_of_sylow hm hS (P.subgroupOf S) hS0 ?_ (B.subgroupOf S) ?_
  · intro K hK hK2
    have hmap : K.map S.subtype ≤ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hK hx)
    have hc : Nat.card ↥(K.map S.subtype) = Nat.card ↥K :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective S)
    rw [← hc]
    refine hq _ hmap ?_
    rintro _ ⟨b, hb, rfl⟩
    have hbb := congrArg Subtype.val (hK2 b hb)
    simpa using hbb
  · intro a ha
    exact Subtype.ext (hB2 a (Subgroup.mem_subgroupOf.1 ha))

end Tables

@[expose] def stabS1 : Subgroup S24 :=
  M24g ⊓ MulAction.stabilizer S24 (2 : Fin 24) ⊓ MulAction.stabilizer S24 ({0, 1} : Finset (Fin 24))

theorem duad_smul_pair_eq_iff (σ : S24) :
    σ • ({0, 1} : Finset (Fin 24)) = {0, 1} ↔ (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, Equiv.Perm.smul_def,
    Equiv.Perm.smul_def]
  constructor
  · intro h
    have ha : σ 0 ∈ ({0, 1} : Finset (Fin 24)) := h ▸ Finset.mem_insert_self _ _
    have hb : σ 1 ∈ ({0, 1} : Finset (Fin 24)) :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    have hne : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hne
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact absurd (ha.trans hb.symm) hne
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · rw [h0, h1]
    · rw [h0, h1]
      exact Finset.pair_comm 1 0

theorem mem_stabS1 {σ : S24} : σ ∈ stabS1 ↔
    σ ∈ M24g ∧ σ 2 = 2 ∧ ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) := by
  unfold stabS1
  rw [Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, duad_smul_pair_eq_iff]
  tauto

theorem exists_swap01 : ∃ σ ∈ stabS1, σ 0 = 1 := by
  obtain ⟨p, hp, h0, h1, h2, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_four 1 0 2 3 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨p, mem_stabS1.2 ⟨hp, h2, Or.inr ⟨h0, h1⟩⟩, h0⟩

section OrderS1

open CFSG.Monster.B.TwoA (Ppair Rest mem_Ppair_iff natCard_Ppair natCard_rest
  isMultiplyPretransitive_rest coe_smul_rest)

attribute [local instance] CFSG.Monster.B.TwoA.restAction


theorem natCard_stabS1 : Nat.card stabS1 = 40320 := by
  haveI : MulAction.IsMultiplyPretransitive ↥Ppair Rest 2 := isMultiplyPretransitive_rest
  haveI : MulAction.IsPretransitive ↥Ppair Rest := MulAction.isPretransitive_of_is_two_pretransitive
  let x2 : Rest := ⟨2, by decide, by decide⟩
  have h1 : (MulAction.stabilizer ↥Ppair x2).index = 22 := by
    rw [MulAction.index_stabilizer_of_transitive, natCard_rest]
  have h2 := (MulAction.stabilizer ↥Ppair x2).card_mul_index
  rw [h1, natCard_Ppair] at h2
  have h3 : Nat.card (MulAction.stabilizer ↥Ppair x2) = 40320 := by omega
  let φ : ↥Ppair →* S24 := AutPerm.subtype.comp Ppair.subtype
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  have hmap : (MulAction.stabilizer ↥Ppair x2).map φ = stabS1 := by
    ext σ
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h2x : (φ p) 2 = 2 := by
        have := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hp)
        rw [coe_smul_rest] at this
        exact this
      exact mem_stabS1.2 ⟨p.1.2, h2x, (mem_Ppair_iff p.1).1 p.2⟩
    · intro hσ
      obtain ⟨hM, h2x, hpair⟩ := mem_stabS1.1 hσ
      refine ⟨⟨⟨σ, hM⟩, (mem_Ppair_iff _).2 hpair⟩, MulAction.mem_stabilizer_iff.2 ?_, rfl⟩
      apply Subtype.ext
      rw [coe_smul_rest]
      exact h2x
  rw [← hmap, Subgroup.card_map_of_injective hφ, h3]


theorem card_le_sixteen_stabS1 (B : Subgroup S24) (hB : B ≤ stabS1)
    (hB2 : ∀ b ∈ B, b * b = 1) : Nat.card B ≤ 16 := by
  have hm : Native.duadP1Gens.length = 3 := rfl
  have hGrp := duadCheck_parts.2.2.1
  have hEa := duadCheck_parts.2.2.2.1
  have hP1 : Subgroup.closure (Set.range duadP1Perm) ≤ stabS1 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    refine mem_stabS1.2 ⟨duadP1Perm_mem j, ?_, ?_⟩
    · revert j
      decide
    · revert j
      decide
  refine duad_card_le_sixteen_of_sylow_sub (m := 315) (by decide) (by rw [natCard_stabS1]; norm_num)
    hP1 (by rw [duadGrp_card hm repT_duadP1Perm hGrp]; norm_num) ?_ B hB hB2
  intro K hK hK2
  exact duadGrp_ea hm repT_duadP1Perm hGrp hEa hK hK2

end OrderS1

@[expose] noncomputable def f770 : W11 := setClass {0, 3, 4, 5}

section F770


theorem isSextClass_f770 : IsSextClass f770 :=
  duad_isSextClass_of_card_four (by decide)

theorem isSextClass_f770_mul : IsSextClass (f770 * setClass {0, 1}) := by
  unfold f770
  rw [duad_setClass_mul]
  exact duad_isSextClass_of_card_four (by decide)

end F770

theorem duad_rho_inv_rho {σ : S24} (hσ : σ ∈ M24g) (w : W11) :
    rho11 AutPerm le_rfl ⟨σ⁻¹, (M24g.inv_mem hσ : σ⁻¹ ∈ AutPerm)⟩
      (rho11 AutPerm le_rfl ⟨σ, hσ⟩ w) = w := by
  have h1 : (⟨σ⁻¹, (M24g.inv_mem hσ : σ⁻¹ ∈ AutPerm)⟩ : ↥AutPerm) * ⟨σ, hσ⟩ = 1 :=
    Subtype.ext (inv_mul_cancel σ)
  rw [← MulAut.mul_apply, ← map_mul, h1, map_one, MulAut.one_apply]

theorem duad_W11_mul_mul_self (a b : W11) : a * b * b = a := by
  rw [mul_assoc, W11_mul_self, mul_one]

theorem duad_rho_t0 {σ : S24} (hσ : σ ∈ M24g) (hs : σ • ({0, 1} : Finset (Fin 24)) = {0, 1}) :
    rho11 AutPerm le_rfl ⟨σ, hσ⟩ (setClass {0, 1}) = setClass {0, 1} := by
  have h := setClass_smul hσ (T := ({0, 1} : Finset (Fin 24))) (by decide)
  rw [hs] at h
  exact h.symm

@[expose] noncomputable def stabS2 : Subgroup S24 where
  carrier := {σ | ∃ hσ : σ ∈ M24g, σ • ({0, 1} : Finset (Fin 24)) = {0, 1} ∧
    (rho11 AutPerm le_rfl ⟨σ, hσ⟩ f770 = f770 ∨
      rho11 AutPerm le_rfl ⟨σ, hσ⟩ f770 = f770 * setClass {0, 1})}
  mul_mem' := by
    rintro σ τ ⟨hσ, hsσ, hfσ⟩ ⟨hτ, hsτ, hfτ⟩
    refine ⟨M24g.mul_mem hσ hτ, ?_, ?_⟩
    · rw [mul_smul, hsτ, hsσ]
    · have e : rho11 AutPerm le_rfl (⟨σ, hσ⟩ * ⟨τ, hτ⟩ : ↥AutPerm) f770 =
          rho11 AutPerm le_rfl ⟨σ, hσ⟩ (rho11 AutPerm le_rfl ⟨τ, hτ⟩ f770) := by
        rw [map_mul]
        rfl
      change rho11 AutPerm le_rfl (⟨σ, hσ⟩ * ⟨τ, hτ⟩ : ↥AutPerm) f770 = f770 ∨
        rho11 AutPerm le_rfl (⟨σ, hσ⟩ * ⟨τ, hτ⟩ : ↥AutPerm) f770 = f770 * setClass {0, 1}
      rw [e]
      rcases hfτ with h | h
      · rw [h]
        exact hfσ
      · rw [h, map_mul, duad_rho_t0 hσ hsσ]
        rcases hfσ with h' | h'
        · rw [h']
          exact Or.inr rfl
        · rw [h', duad_W11_mul_mul_self]
          exact Or.inl rfl
  one_mem' := by
    refine ⟨M24g.one_mem, by rw [one_smul], Or.inl ?_⟩
    have h1 : (⟨1, M24g.one_mem⟩ : ↥AutPerm) = 1 := rfl
    rw [h1, map_one]
    rfl
  inv_mem' := by
    rintro σ ⟨hσ, hs, hf⟩
    have hs' : σ⁻¹ • ({0, 1} : Finset (Fin 24)) = {0, 1} := inv_smul_eq_iff.2 hs.symm
    have hσ' : σ⁻¹ ∈ M24g := M24g.inv_mem hσ
    refine ⟨hσ', hs', ?_⟩
    have h0 := duad_rho_inv_rho hσ f770
    change rho11 AutPerm le_rfl ⟨σ⁻¹, hσ'⟩ f770 = f770 ∨
      rho11 AutPerm le_rfl ⟨σ⁻¹, hσ'⟩ f770 = f770 * setClass {0, 1}
    rcases hf with h | h
    · rw [h] at h0
      exact Or.inl h0
    · rw [h, map_mul, duad_rho_t0 hσ' hs'] at h0
      refine Or.inr ?_
      calc rho11 AutPerm le_rfl ⟨σ⁻¹, hσ'⟩ f770
          = rho11 AutPerm le_rfl ⟨σ⁻¹, hσ'⟩ f770 * setClass {0, 1} * setClass {0, 1} :=
            (duad_W11_mul_mul_self _ _).symm
        _ = f770 * setClass {0, 1} := by
          rw [h0]

theorem mem_stabS2 {σ : S24} : σ ∈ stabS2 ↔ ∃ hσ : σ ∈ M24g,
    σ • ({0, 1} : Finset (Fin 24)) = {0, 1} ∧
    (rho11 AutPerm le_rfl ⟨σ, hσ⟩ f770 = f770 ∨
      rho11 AutPerm le_rfl ⟨σ, hσ⟩ f770 = f770 * setClass {0, 1}) := Iff.rfl

theorem duad_setClass_pair_eq (a b : Fin 24) :
    setClass {a, b} = toW 11 (Native.duadMask (a : ℕ) (b : ℕ)) := by
  rw [← duad_maskFin a b, setClass_maskFin]
  exact congrArg (toW 11) (actM_eq_actM _ _).symm

theorem toW_duadT0 : toW 11 (Native.duadT0 ()) = setClass {0, 1} := (duad_setClass_pair_eq 0 1).symm

theorem toW_duadMask02 : toW 11 (Native.duadMask 0 2) = setClass {0, 2} :=
  (duad_setClass_pair_eq 0 2).symm

theorem toW_duadF770 : toW 11 (Native.duadF770 ()) = f770 := by
  have h := maskFin_tetrad 3 4 5
  unfold f770
  rw [← h, setClass_maskFin]
  exact congrArg (toW 11) (actM_eq_actM _ _)

theorem duadT0_lt : Native.duadT0 () < 2 ^ 11 := by
  unfold Native.duadT0 Native.duadMask
  rw [actM_eq_actM]
  exact actM_lt ccECols_lt _

section PairOrbit

open CFSG.Monster.B.TwoA (Ppair mem_Ppair_iff natCard_Ppair)


theorem duadPpPerm_pair : ∀ j : Fin 2,
    (duadPpPerm j 0 = 0 ∧ duadPpPerm j 1 = 1) ∨ (duadPpPerm j 0 = 1 ∧ duadPpPerm j 1 = 0) := by
  decide

noncomputable def duadPpGen (j : Fin 2) : ↥Ppair :=
  ⟨⟨duadPpPerm j, duadPpPerm_mem j⟩, (mem_Ppair_iff _).2 (duadPpPerm_pair j)⟩

theorem duadPpGen_smul (j : Fin 2) (w : W11) :
    duadPpGen j • w = rho11 AutPerm le_rfl ⟨duadPpPerm j, duadPpPerm_mem j⟩ w := by
  rw [Subgroup.smul_def]
  exact duad_smul_def _ _

noncomputable def duadPairOf (m : ℕ) : Finset W11 := {toW 11 m, toW 11 m * setClass {0, 1}}

theorem duadPairOf_step (j : Fin 2) (a : ℕ) :
    duadPairOf (Native.toddAct (Native.duadPpGens.getD j #[]) a) = duadPpGen j • duadPairOf a := by
  have hs := (duad_smul_pair_eq_iff (duadPpPerm j)).2 (duadPpPerm_pair j)
  have h1 := rho11_toW_native (duadPpPerm_mem j) (repT_duadPpPerm j) a
  have h2 := duad_rho_t0 (duadPpPerm_mem j) hs
  unfold duadPairOf
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, duadPpGen_smul, duadPpGen_smul,
    map_mul,
    h1, h2]

noncomputable def duadC0 : Finset W11 := {f770, f770 * setClass {0, 1}}

theorem duadPairOf_f770 : duadPairOf (Native.duadF770 ()) = duadC0 := by
  unfold duadPairOf duadC0
  rw [toW_duadF770]

theorem duad_pairKey_eq_of_pairOf_eq {x y : ℕ} (hx : x < 2 ^ 11) (hy : y < 2 ^ 11)
    (h : duadPairOf x = duadPairOf y) :
    Native.duadPairKey (Native.duadT0 ()) x = Native.duadPairKey (Native.duadT0 ()) y := by
  have ht0 := duadT0_lt
  have hxt : x ^^^ Native.duadT0 () < 2 ^ 11 := Nat.xor_lt_two_pow hx ht0
  have hyt : y ^^^ Native.duadT0 () < 2 ^ 11 := Nat.xor_lt_two_pow hy ht0
  have hmem : toW 11 x ∈ duadPairOf y := by
    rw [← h]
    unfold duadPairOf
    exact Finset.mem_insert_self _ _
  unfold duadPairOf at hmem
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · rw [toW_inj hx hy h1]
  · rw [← toW_duadT0, ← toW_xor] at h1
    have h2 : x = y ^^^ Native.duadT0 () := toW_inj hx hyt h1
    unfold Native.duadPairKey
    rw [h2, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, min_comm]

theorem duad_orbit_c0_ge : 770 ≤ (MulAction.orbit ↥Ppair duadC0).ncard := by
  classical
  obtain ⟨r, hr, hsz, hnd⟩ : ∃ r : Array ℕ × Array ℕ × Array ℕ,
      Native.treeValid (fun m => decide (m < 2048))
        (Native.duadPpGens.map fun g m => Native.toddAct g m) (Native.duadF770 ()) r = true ∧
      770 ≤ r.1.size ∧
      (r.1.toList.map (Native.duadPairKey (Native.duadT0 ()))).Nodup := by
    have h := duadCheck_parts.2.1
    unfold Native.duadPairOrbitCheck at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, h.1.1, h.1.2, h.2⟩
  have key := exists_smul_of_tree (G := ↥Ppair) (X := Finset W11) ⊤ duadPpGen
    (fun j => Subgroup.mem_top _) (valid := fun m => decide (m < 2048))
    (steps := Native.duadPpGens.map fun g m => Native.toddAct g m)
    (by simp [Native.duadPpGens]) duadPairOf
    (fun j a _ => by
      rw [getD_map_of_lt _ Native.duadPpGens #[] id j.2]
      exact duadPairOf_step j a) hr
  set c := r.1.toList with hc
  have hcnd : c.Nodup := List.Nodup.of_map _ hnd
  have hvalid := treeValid_valid hr
  have hsub : ((c.toFinset.image duadPairOf : Finset (Finset W11)) : Set (Finset W11)) ⊆
      MulAction.orbit ↥Ppair duadC0 := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨σ, -, hσq⟩ := key q (List.mem_toFinset.1 hq)
    exact ⟨σ, by rw [← duadPairOf_f770]; exact hσq⟩
  have hcard : (c.toFinset.image duadPairOf).card = c.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hcnd]
    intro x hx y hy hxy
    have hx' : x < 2048 := by simpa using hvalid x (List.mem_toFinset.1 hx)
    have hy' : y < 2048 := by simpa using hvalid y (List.mem_toFinset.1 hy)
    exact List.inj_on_of_nodup_map hnd (List.mem_toFinset.1 hx) (List.mem_toFinset.1 hy)
      (duad_pairKey_eq_of_pairOf_eq (by simpa using hx') (by simpa using hy') hxy)
  calc 770 ≤ c.length := by simpa [hc] using hsz
    _ = (↑(c.toFinset.image duadPairOf) : Set (Finset W11)).ncard := by
        rw [Set.ncard_coe_finset, hcard]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end PairOrbit

section OrderS2

open CFSG.Monster.B.TwoA (Ppair mem_Ppair_iff natCard_Ppair)


theorem duad_ppair_smul_def (p : ↥Ppair) (w : W11) : p • w = rho11 AutPerm le_rfl p.1 w := by
  rw [Subgroup.smul_def]
  exact duad_smul_def _ _

theorem duad_smul_c0 (p : ↥Ppair) : p • duadC0 = {rho11 AutPerm le_rfl p.1 f770,
    rho11 AutPerm le_rfl p.1 f770 * setClass {0, 1}} := by
  have h : rho11 AutPerm le_rfl p.1 (setClass {0, 1}) = setClass {0, 1} :=
    duad_rho_t0 p.1.2 ((duad_smul_pair_eq_iff _).2 ((mem_Ppair_iff p.1).1 p.2))
  unfold duadC0
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, duad_ppair_smul_def,
    duad_ppair_smul_def,
    map_mul, h]

theorem duad_stabS2_eq_map : stabS2 =
    (MulAction.stabilizer ↥Ppair duadC0).map (AutPerm.subtype.comp Ppair.subtype) := by
  ext σ
  constructor
  · rintro ⟨hσ, hs, hf⟩
    have hP : (⟨σ, hσ⟩ : ↥AutPerm) ∈ Ppair := (mem_Ppair_iff _).2 ((duad_smul_pair_eq_iff σ).1 hs)
    refine ⟨⟨⟨σ, hσ⟩, hP⟩, MulAction.mem_stabilizer_iff.2 ?_, rfl⟩
    rw [duad_smul_c0]
    rcases hf with h | h
    · dsimp only
      rw [h]
      rfl
    · dsimp only
      rw [h, duad_W11_mul_mul_self]
      exact Finset.pair_comm _ _
  · rintro ⟨p, hp, rfl⟩
    have hpc := MulAction.mem_stabilizer_iff.1 hp
    rw [duad_smul_c0] at hpc
    have hmem : rho11 AutPerm le_rfl p.1 f770 ∈ duadC0 := by
      rw [← hpc]
      exact Finset.mem_insert_self _ _
    unfold duadC0 at hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    exact ⟨p.1.2, (duad_smul_pair_eq_iff _).2 ((mem_Ppair_iff p.1).1 p.2), hmem⟩

theorem natCard_stabS2_le : Nat.card stabS2 ≤ 1152 := by
  have hφ : Function.Injective (AutPerm.subtype.comp Ppair.subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have h1 := (MulAction.stabilizer ↥Ppair duadC0).card_mul_index
  rw [MulAction.index_stabilizer, natCard_Ppair] at h1
  have h2 := duad_orbit_c0_ge
  have h3 := Nat.mul_le_mul_left (Nat.card (MulAction.stabilizer ↥Ppair duadC0)) h2
  rw [h1] at h3
  rw [duad_stabS2_eq_map, Subgroup.card_map_of_injective hφ]
  generalize Nat.card (MulAction.stabilizer ↥Ppair duadC0) = a at h3 ⊢
  omega

theorem duadP2Perm_mem_stabS2 (j : Fin 3) : duadP2Perm j ∈ stabS2 := by
  refine ⟨duadP2Perm_mem j, (duad_smul_pair_eq_iff _).2 ?_, ?_⟩
  · revert j
    decide
  · have hS2 := duadCheck_parts.2.2.2.2.2.2.2.1
    unfold Native.duadS2Check at hS2
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.mem_append] at hS2
    have hj : (j : ℕ) < Native.duadP2Gens.length := j.2
    have hmem : Native.duadP2Gens.getD j #[] ∈ Native.duadP2Gens := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have h := hS2 _ (Or.inl hmem)
    have hr := rho11_toW_native (duadP2Perm_mem j) (repT_duadP2Perm j) (Native.duadF770 ())
    rw [toW_duadF770] at hr
    rcases h with h | h
    · left
      rw [hr, h, toW_duadF770]
    · right
      rw [hr, h, toW_xor, toW_duadF770, toW_duadT0]

theorem duadQ3Perm_mem_stabS2 (j : Fin 2) : duadQ3Perm j ∈ stabS2 := by
  refine ⟨duadQ3Perm_mem j, (duad_smul_pair_eq_iff _).2 ?_, ?_⟩
  · revert j
    decide
  · have hS2 := duadCheck_parts.2.2.2.2.2.2.2.1
    unfold Native.duadS2Check at hS2
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.mem_append] at hS2
    have hj : (j : ℕ) < Native.duadQ3Gens.length := j.2
    have hmem : Native.duadQ3Gens.getD j #[] ∈ Native.duadQ3Gens := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have h := hS2 _ (Or.inr hmem)
    have hr := rho11_toW_native (duadQ3Perm_mem j) (repT_duadQ3Perm j) (Native.duadF770 ())
    rw [toW_duadF770] at hr
    rcases h with h | h
    · left
      rw [hr, h, toW_duadF770]
    · right
      rw [hr, h, toW_xor, toW_duadF770, toW_duadT0]

theorem natCard_stabS2 : Nat.card stabS2 = 1152 := by
  have hGrp2 := duadCheck_parts.2.2.2.2.1
  have hGrp3 := duadCheck_parts.2.2.2.2.2.2.1
  have hP2 : Subgroup.closure (Set.range duadP2Perm) ≤ stabS2 :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨j, rfl⟩
      exact duadP2Perm_mem_stabS2 j)
  have hQ3 : Subgroup.closure (Set.range duadQ3Perm) ≤ stabS2 :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨j, rfl⟩
      exact duadQ3Perm_mem_stabS2 j)
  have h1 := Subgroup.card_dvd_of_le hP2
  have h2 := Subgroup.card_dvd_of_le hQ3
  rw [duadGrp_card (show Native.duadP2Gens.length = 3 from rfl) repT_duadP2Perm hGrp2] at h1
  rw [duadGrp_card (show Native.duadQ3Gens.length = 2 from rfl) repT_duadQ3Perm hGrp3] at h2
  have h3 := natCard_stabS2_le
  have h4 : 0 < Nat.card stabS2 := Nat.card_pos
  have h5 : 128 * 9 ∣ Nat.card stabS2 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
  omega

theorem card_le_sixteen_stabS2 (B : Subgroup S24) (hB : B ≤ stabS2)
    (hB2 : ∀ b ∈ B, b * b = 1) : Nat.card B ≤ 16 := by
  have hm : Native.duadP2Gens.length = 3 := rfl
  have hGrp := duadCheck_parts.2.2.2.2.1
  have hEa := duadCheck_parts.2.2.2.2.2.1
  have hP2 : Subgroup.closure (Set.range duadP2Perm) ≤ stabS2 :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨j, rfl⟩
      exact duadP2Perm_mem_stabS2 j)
  refine duad_card_le_sixteen_of_sylow_sub (m := 9) (by decide) (by rw [natCard_stabS2]; norm_num)
    hP2 (by rw [duadGrp_card hm repT_duadP2Perm hGrp]; norm_num) ?_ B hB hB2
  intro K hK hK2
  exact duadGrp_ea hm repT_duadP2Perm hGrp hEa hK hK2

end OrderS2

@[expose] noncomputable def x1120 : W11 := setClass {0, 3, 4, 8}

theorem toW_duadX1120 : toW 11 (Native.duadX1120 ()) = x1120 := by
  have h := maskFin_tetrad 3 4 8
  unfold x1120
  rw [← h, setClass_maskFin]
  exact congrArg (toW 11) (actM_eq_actM _ _)

section X1120


theorem isSextClass_x1120 : IsSextClass x1120 :=
  duad_isSextClass_of_card_four (by decide)

end X1120

section X1120Sat


theorem x1120_sat : ∀ u ∈ ({setClass {0, 1}, setClass {0, 2}, setClass {0, 1} * setClass {0, 2}} :
    Set W11), ∃ σ ∈ stabS1, ∃ hσ : σ ∈ M24g, rho11 AutPerm le_rfl ⟨σ, hσ⟩ x1120 = x1120 * u := by
  have hsat := duadCheck_parts.2.2.2.2.2.2.2.2
  unfold Native.duadSatCheck at hsat
  simp only [Bool.and_eq_true, beq_iff_eq] at hsat
  obtain ⟨⟨⟨-, e0⟩, e1⟩, e2⟩ := hsat
  have key : ∀ j : Fin 3, duadXPerm j ∈ stabS1 := fun j =>
    mem_stabS1.2 ⟨duadXPerm_mem j, by revert j; decide, Or.inl (by revert j; decide)⟩
  have hact : ∀ (j : Fin 3) (m : ℕ),
      rho11 AutPerm le_rfl ⟨duadXPerm j, duadXPerm_mem j⟩ (toW 11 m) =
      toW 11 (Native.toddAct (Native.duadXWit.getD j #[]) m) := fun j m =>
    rho11_toW_native (duadXPerm_mem j) (repT_duadXPerm j) m
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · refine ⟨duadXPerm 0, key 0, duadXPerm_mem 0, ?_⟩
    have h := congrArg (toW 11) e0
    rw [toW_xor, toW_duadT0] at h
    rw [← toW_duadX1120, hact 0]
    exact h
  · refine ⟨duadXPerm 1, key 1, duadXPerm_mem 1, ?_⟩
    have h := congrArg (toW 11) e1
    rw [toW_xor, toW_duadMask02] at h
    rw [← toW_duadX1120, hact 1]
    exact h
  · refine ⟨duadXPerm 2, key 2, duadXPerm_mem 2, ?_⟩
    have h := congrArg (toW 11) e2
    rw [toW_xor, toW_xor, toW_duadT0, toW_duadMask02] at h
    rw [← toW_duadX1120, hact 2]
    exact h

end X1120Sat

end CFSG.Quasithin.H13.AS91.M24G
