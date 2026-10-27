module

public import CFSG.Timmesfeld.Moufang.A6
public import CFSG.Timmesfeld.Moufang.J2Check
public import CFSG.Timmesfeld.Moufang.J2MatCheck
public import Certificates.Certificate15953

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration
open CFSG.Sporadic.Bridge.J2 (seedGroup natU idL wfM mulL toM unitL lwordL uA uB wfM_idL natX_wf
  natXi_wf natU_val natU_inv natU_mem val_natWord natWord_mem val_wordProd_of_lwordL
  wordProd_eq_one_of_lwordL le_card_seedGroup nativeEquiv)

namespace J2

abbrev Pres : Type := PresentedGroup (wordRels (lineRels 5 true))

theorem signedProd_comp {G : Type*} [Group G] {m k : ℕ} (x : Fin k → G) (f : Fin m → Fin k)
    (w : List (Fin m × Bool)) :
    signedProd (x ∘ f) w = signedProd x (w.map fun l => (f l.1, l.2)) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [signedProd_cons, List.map_cons, signedProd_cons, ih]
    rfl

theorem map_lineRels_two :
    ∀ w ∈ lineRels 2 false, (w.map fun l => (emb l.1, l.2)) ∈ lineRels 5 true :=
  Certificates.certificate15953.1

noncomputable def fromA6 : A6.Pres →* Pres :=
  wordsHom (lineRels 2 false) (fun j => PresentedGroup.of (emb j)) (fun w hw => by
    rw [show (fun j => (PresentedGroup.of (emb j) : Pres)) = PresentedGroup.of ∘ emb from rfl,
      signedProd_comp]
    exact signedProd_of_eq_one (map_lineRels_two w hw))

noncomputable abbrev sub : Subgroup Pres := fromA6.range

theorem card_sub_le : Finite sub ∧ Nat.card sub ≤ 1080 := by
  obtain ⟨hfin, hcard⟩ := A6.card_pres_le
  exact ⟨Finite.of_surjective _ fromA6.rangeRestrict_surjective,
    (Nat.card_le_card_of_surjective _ fromA6.rangeRestrict_surjective).trans hcard⟩

@[expose] def subWords : List (List (Fin 7 × Bool)) :=
  [[(0, true)], [(1, true)], [(2, true)], [(3, true)]]

theorem codes_subWords : codes subWords = [[0], [2], [4], [6]] := by decide

theorem subWords_mem :
    ∀ w ∈ subWords, PresentedGroup.mk (wordRels (lineRels 5 true)) (FreeGroup.mk w) ∈ sub := by
  intro w hw
  simp only [subWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact ⟨PresentedGroup.of 0, by rw [fromA6, wordsHom_of]; rfl⟩
  · exact ⟨PresentedGroup.of 1, by rw [fromA6, wordsHom_of]; rfl⟩
  · exact ⟨PresentedGroup.of 2, by rw [fromA6, wordsHom_of]; rfl⟩
  · exact ⟨PresentedGroup.of 3, by rw [fromA6, wordsHom_of]; rfl⟩

theorem index_sub_le : sub.FiniteIndex ∧ sub.index ≤ 560 := by
  have h := index_le_of_facts_presented (H := sub) (N := 560) (F := 3920)
    (fx := J2Data.fx) (fc := J2Data.fc) (fy := J2Data.fy) (kind := J2Data.kind)
    (wi := J2Data.wi) (fs := J2Data.fs) (ft := J2Data.ft) (fo := J2Data.fo)
    (refs := J2Data.refs) (pl := J2Data.pl) (ffi := J2Data.ffi) (live := J2Data.live)
    (lineRels 5 true) subWords J2Data.words (fun w hw => ⟨w, hw, rfl⟩) subWords_mem
    Certificates.certificate15953.2 J2Data.live_zero (by norm_num)
    (by rw [codes_subWords]; exact J2Data.facts_all) J2Data.cover_all
  rw [J2Data.liveCount_eq] at h
  exact h

theorem card_pres_le : Finite Pres ∧ Nat.card Pres ≤ 604800 := by
  obtain ⟨hfi, hidx⟩ := index_sub_le
  obtain ⟨hfin, hcard⟩ := card_sub_le
  have h := sub.card_mul_index
  have hpos : 0 < Nat.card sub := Nat.card_pos
  have hne : Nat.card Pres ≠ 0 := by
    rw [← h]
    exact Nat.mul_ne_zero hpos.ne' hfi.index_ne_zero
  refine ⟨Nat.finite_of_card_ne_zero hne, ?_⟩
  rw [← h]
  calc Nat.card sub * sub.index ≤ 1080 * 560 := Nat.mul_le_mul hcard hidx
    _ = 604800 := by norm_num

theorem genL_wf (i : ℕ) : wfM (genL i) = true := by
  match i with
  | 0 => exact genL_wf_0
  | 1 => exact genL_wf_1
  | 2 => exact genL_wf_2
  | 3 => exact genL_wf_3
  | 4 => exact genL_wf_4
  | 5 => exact genL_wf_5
  | 6 => exact genL_wf_6
  | _ + 7 => exact wfM_idL

theorem genL_sq (i : ℕ) : mulL (genL i) (genL i) = idL := by
  match i with
  | 0 => exact genL_sq_0
  | 1 => exact genL_sq_1
  | 2 => exact genL_sq_2
  | 3 => exact genL_sq_3
  | 4 => exact genL_sq_4
  | 5 => exact genL_sq_5
  | 6 => exact genL_sq_6
  | _ + 7 => exact mulL_idL_idL

@[expose] noncomputable def unitGen (i : ℕ) : GL (Fin 14) (ZMod 5) :=
  unitL (genL i) (genL i) (genL_wf i) (genL_wf i) (genL_sq i) (genL_sq i)

theorem unitGen_val (i : ℕ) :
    (unitGen i : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (genL i) := rfl

theorem unitGen_inv (i : ℕ) :
    (((unitGen i)⁻¹ : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM (genL i) := rfl

theorem unitGen_zero_eq : unitGen 0 = CFSG.Sporadic.Bridge.wordProd natU wordD :=
  Units.ext (val_natWord lwordL_wordD).symm

theorem unitGen_zero_mem : unitGen 0 ∈ seedGroup := by
  rw [unitGen_zero_eq]
  exact natWord_mem _

@[expose] noncomputable def unitABD : ℕ → GL (Fin 14) (ZMod 5)
  | 0 => uA
  | 1 => uB
  | _ + 2 => unitGen 0

theorem letterABD_wf (i : ℕ) : wfM (letterABD i) = true := by
  match i with
  | 0 => exact natX_wf 0
  | 1 => exact natX_wf 1
  | _ + 2 => exact genL_wf 0

theorem letterABDInv_wf (i : ℕ) : wfM (letterABDInv i) = true := by
  match i with
  | 0 => exact natXi_wf 0
  | 1 => exact natXi_wf 1
  | _ + 2 => exact genL_wf 0

theorem unitABD_val (i : ℕ) :
    (unitABD i : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (letterABD i) := by
  match i with
  | 0 => exact natU_val 0
  | 1 => exact natU_val 1
  | _ + 2 => rfl

theorem unitABD_inv (i : ℕ) :
    (((unitABD i)⁻¹ : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM (letterABDInv i) := by
  match i with
  | 0 => exact natU_inv 0
  | 1 => exact natU_inv 1
  | _ + 2 => rfl

theorem unitABD_mem (i : ℕ) : unitABD i ∈ seedGroup := by
  match i with
  | 0 => exact natU_mem 0
  | 1 => exact natU_mem 1
  | _ + 2 => exact unitGen_zero_mem

theorem lwordL_genWord (i : ℕ) :
    lwordL letterABD letterABDInv (genWord (i + 1)) idL = genL (i + 1) := by
  match i with
  | 0 => exact lwordL_genWord_1
  | 1 => exact lwordL_genWord_2
  | 2 => exact lwordL_genWord_3
  | 3 => exact lwordL_genWord_4
  | 4 => exact lwordL_genWord_5
  | 5 => exact lwordL_genWord_6
  | _ + 6 => rfl

theorem unitGen_succ_eq (i : ℕ) :
    unitGen (i + 1) = CFSG.Sporadic.Bridge.wordProd unitABD (genWord (i + 1)) :=
  Units.ext (val_wordProd_of_lwordL letterABD_wf letterABDInv_wf unitABD_val unitABD_inv
    (lwordL_genWord i)).symm

theorem unitGen_mem (i : ℕ) : unitGen i ∈ seedGroup := by
  match i with
  | 0 => exact unitGen_zero_mem
  | i + 1 =>
    rw [unitGen_succ_eq]
    exact CFSG.Sporadic.Bridge.wordProd_mem unitABD_mem _

@[expose] noncomputable def nativeGens (j : Fin 7) : ↥seedGroup :=
  ⟨unitGen j.val, unitGen_mem j.val⟩

theorem coe_signedProd_nativeGens (w : List (Fin 7 × Bool)) :
    ((signedProd nativeGens w : ↥seedGroup) : GL (Fin 14) (ZMod 5)) =
      CFSG.Sporadic.Bridge.wordProd unitGen (w.map fun l => (l.1.val, l.2)) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨j, b⟩ := l
    rw [signedProd_cons, Subgroup.coe_mul, ih]
    cases b <;> simp [CFSG.Sporadic.Bridge.wordProd, nativeGens]

theorem lwordL_relators :
    ∀ w ∈ lineRels 5 true, lwordL genL genL (w.map fun l => (l.1.val, l.2)) idL = idL := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hw
  have e : ((lineRels 5 true)[k]).map (fun l => (l.1.val, l.2)) = relL k := by
    rw [relL, List.getD_eq_getElem _ _ hk]
  rw [e]
  have hk' : k < 34 := length_lineRels ▸ hk
  interval_cases k
  · exact relL_0
  · exact relL_1
  · exact relL_2
  · exact relL_3
  · exact relL_4
  · exact relL_5
  · exact relL_6
  · exact relL_7
  · exact relL_8
  · exact relL_9
  · exact relL_10
  · exact relL_11
  · exact relL_12
  · exact relL_13
  · exact relL_14
  · exact relL_15
  · exact relL_16
  · exact relL_17
  · exact relL_18
  · exact relL_19
  · exact relL_20
  · exact relL_21
  · exact relL_22
  · exact relL_23
  · exact relL_24
  · exact relL_25
  · exact relL_26
  · exact relL_27
  · exact relL_28
  · exact relL_29
  · exact relL_30
  · exact relL_31
  · exact relL_32
  · exact relL_33

theorem nativeGens_relators : ∀ w ∈ lineRels 5 true, signedProd nativeGens w = 1 := by
  intro w hw
  apply Subtype.ext
  rw [coe_signedProd_nativeGens, Subgroup.coe_one]
  exact wordProd_eq_one_of_lwordL genL_wf genL_wf unitGen_val unitGen_inv (lwordL_relators w hw)

noncomputable def toSeed : Pres →* ↥seedGroup :=
  wordsHom (lineRels 5 true) nativeGens nativeGens_relators

theorem uA_eq : uA = CFSG.Sporadic.Bridge.wordProd unitGen (wordA.map fun l => (l.1.val, l.2)) :=
  Units.ext (val_wordProd_of_lwordL genL_wf genL_wf unitGen_val unitGen_inv lwordL_wordA).symm

theorem uB_eq : uB = CFSG.Sporadic.Bridge.wordProd unitGen (wordB.map fun l => (l.1.val, l.2)) :=
  Units.ext (val_wordProd_of_lwordL genL_wf genL_wf unitGen_val unitGen_inv lwordL_wordB).symm

theorem toSeed_surjective : Function.Surjective toSeed := by
  have hw : ∀ w : List (Fin 7 × Bool), ∃ x, ((toSeed x : ↥seedGroup) : GL (Fin 14) (ZMod 5)) =
      CFSG.Sporadic.Bridge.wordProd unitGen (w.map fun l => (l.1.val, l.2)) := fun w =>
    ⟨signedProd PresentedGroup.of w, by rw [toSeed, wordsHom_signedProd, coe_signedProd_nativeGens]⟩
  have key : ∀ z ∈ seedGroup, ∃ x, ((toSeed x : ↥seedGroup) : GL (Fin 14) (ZMod 5)) = z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · obtain ⟨x, hx⟩ := hw wordA
        exact ⟨x, hx.trans uA_eq.symm⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨x, hx⟩ := hw wordB
        exact ⟨x, hx.trans uB_eq.symm⟩
    | one => exact ⟨1, by rw [map_one, Subgroup.coe_one]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a * b, by rw [map_mul, Subgroup.coe_mul, ha, hb]⟩
    | inv x _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨a⁻¹, by rw [map_inv, Subgroup.coe_inv, ha]⟩
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := key y hy
  exact ⟨x, Subtype.ext hx⟩

theorem nonempty_mulEquiv : Nonempty (Pres ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have := card_pres_le.1
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.nonempty_mulEquiv_of_surjective toSeed toSeed_surjective
    card_pres_le.2 le_card_seedGroup
  exact ⟨e.symm.trans nativeEquiv.symm⟩

theorem isSimpleGroup_pres : IsSimpleGroup Pres := by
  obtain ⟨e⟩ := nonempty_mulEquiv
  have := CFSG.Sporadic.J2.isSimpleGroup_J2
  exact e.isSimpleGroup

end J2

open J2 in
theorem j2Endgame : J2Endgame := by
  intro H _ d c x hcfg hov hdc hgen
  refine ⟨hcfg.isConj, ?_⟩
  have hovL : signedProd (lineGens d c x) ((List.finRange 5).map letterX) = 1 := by
    rw [show (List.finRange 5).map letterX =
      [letterX 0, letterX 1, letterX 2, letterX 3, letterX 4] by decide]
    simpa [mul_assoc] using hov
  set φ : Pres →* H := wordsHom (lineRels 5 true) (lineGens d c x)
    (hcfg.signedProd_lineRels fun _ => hovL)
  have hφ : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, range_wordsHom, range_lineGens, hgen]
  have := isSimpleGroup_pres
  have hinj : Function.Injective φ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).mp h
    · exfalso
      apply hdc
      obtain ⟨a, ha⟩ := hφ (d * c)
      rw [← ha]
      exact (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top a)
  obtain ⟨e⟩ := nonempty_mulEquiv
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm.trans e⟩

end CFSG.Timmesfeld.Moufang
