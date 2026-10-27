module

public import CFSG.Sporadic.ONOddCore.LiftCands
public import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ON.Native
open CFSG.ComponentClassification.PSL3Four (TabRep)

theorem mem_onMgens_iff
    {g : Equiv.Perm (Fin N)} :
    g ∈ onMgens ↔ ∃ i < 3, g = (hGen i : Equiv.Perm (Fin N)) := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi3 : i < 3 := by rwa [onMgens_length] at hi
    exact ⟨i, hi3, (hGen_val hi3).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [onMgens_length]; exact hi, (hGen_val hi).symm⟩

theorem mem_hGens_iff
    {h : onM} : h ∈ hGens ↔ ∃ i < 3, h = hGen i := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [hGen, List.getD_eq_getElem _ _ hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [hGen, List.getD_eq_getElem _ _ hi]⟩

theorem hGens_closure_top :
    Subgroup.closure {g : onM | g ∈ hGens} = ⊤ := by
  apply Subgroup.map_injective onM.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  conv_rhs => rw [onM]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype, mem_onMgens_iff,
    mem_hGens_iff]
  constructor
  · rintro ⟨h, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hGen i, ⟨i, hi, rfl⟩, rfl⟩

theorem hom_ext_hGens
    {H : Type*} [Group H] {f g : onM →* H}
    (h : ∀ i < 3, f (hGen i) = g (hGen i)) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense hGens_closure_top
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi3 : i < 3 := hi
  have := h i hi3
  rwa [hGen, List.getD_eq_getElem _ _ hi] at this

@[expose] def liftImg
    (e : LiftEntry) (i : ℕ) : onM := evalPos hGens (e.words.getD i [])

theorem lift_form
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    e.words.length = 3 ∧ (∀ w ∈ e.words, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) ∧
      (e.power = 1 ∨ e.power = 3) :=
  (r3e_on_local_automorphism_certificate_data.2.2.2.1 _ (recK_mem hk)).2.2 e he

theorem posArr_size_gen (n : ℕ) (gs : Array (Array ℕ)) (w : List ℕ) : (posArr n gs w).size = n := by
  cases w with
  | nil => exact Array.size_ofFn
  | cons l w => exact Array.size_ofFn

theorem posArr_size (gs : Array (Array ℕ)) (w : List ℕ) : (posArr nPts gs w).size = N :=
  posArr_size_gen nPts gs w

theorem prep_liftArrs
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) {i : ℕ}
    (hi : i < 3) :
    PRep N (liftArrs (wordArrs Data.MWords) e)[i]! (liftImg e i : Equiv.Perm (Fin N)) ∧
      (liftArrs (wordArrs Data.MWords) e)[i]!.size = N := by
  obtain ⟨hl, hw, -⟩ := lift_form hk he
  have hil : i < e.words.length := by rw [hl]; exact hi
  have e1 : (liftArrs (wordArrs Data.MWords) e)[i]! =
      posArr nPts (wordArrs Data.MWords) (e.words.getD i []) := by
    rw [liftArrs, getElem!_pos _ _ (by simpa using hil), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hil]
  rw [e1]
  exact ⟨prep_posArr_h (hw _ (by rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil)),
    posArr_size _ _⟩

theorem liftImg_mem_P
    (e : LiftEntry) (i : ℕ) : (liftImg e i : Equiv.Perm (Fin N)) ∈ Pv :=
  onM_le (liftImg e i).2

theorem hGen_mem_P
    (i : ℕ) : (hGen i : Equiv.Perm (Fin N)) ∈ Pv := onM_le (hGen i).2

@[expose] def liftPair
    (e : LiftEntry) (i : ℕ) : Pv.prod Pv :=
  ⟨((hGen i : Equiv.Perm (Fin N)), (liftImg e i : Equiv.Perm (Fin N))),
    Subgroup.mem_prod.2 ⟨hGen_mem_P i, liftImg_mem_P e i⟩⟩

theorem base3_length : base3.length = 3 := rfl

theorem liftRoot_rel : pairRel N base3 liftRoot 1 := by
  have h := pairRel_root (n := N) base3
  have e : (base3.map Fin.val).toArray = base3Arr := rfl
  rwa [e] at h

theorem liftPairGens_get (hA : Array (Array ℕ)) (e : LiftEntry) {j : ℕ} (hj : j < 3) :
    (liftPairGens hA e)[j]! = dbl nPts hA[j]! (liftArrs hA e)[j]! := by
  interval_cases j <;> rfl

theorem liftPairGens_size (hA : Array (Array ℕ)) (e : LiftEntry) : (liftPairGens hA e).size = 3 :=
  rfl

theorem hA_get_size {i : ℕ} (hi : i < 3) : (wordArrs Data.MWords)[i]!.size = N := by
  rw [wordArrs, pwords_eq,
    getElem!_map' _ _ (by rw [show Data.MWords.size = 3 by decide]; exact hi)]
  exact pword_size _ _ _ _

theorem lift_step
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    ∀ j < (liftPairGens (wordArrs Data.MWords) e).size, ∀ t (g : Pv.prod Pv),
      pairRel N base3 t (g : Equiv.Perm (Fin N) × Equiv.Perm (Fin N)) →
      pairRel N base3 (leftStep 6 (liftPairGens (wordArrs Data.MWords) e) j t)
        ((liftPair e j * g : Pv.prod Pv) : Equiv.Perm (Fin N) × Equiv.Perm (Fin N)) := by
  intro j hj t g ht
  rw [liftPairGens_size] at hj
  obtain ⟨hp, hs⟩ := prep_liftArrs hk he hj
  have h := pairRel_step (prep_hA hj) hp (hA_get_size hj) hs ht
  rw [leftStep, liftPairGens_get _ _ hj]
  exact h

theorem pairRel_inj_P
    {t : Tab} {g g' : Pv.prod Pv}
    (h : pairRel N base3 t (g : Equiv.Perm (Fin N) × Equiv.Perm (Fin N)))
    (h' : pairRel N base3 t (g' : Equiv.Perm (Fin N) × Equiv.Perm (Fin N))) : g = g' := by
  obtain ⟨-, hk⟩ := h
  obtain ⟨-, hk'⟩ := h'
  have hg := Subgroup.mem_prod.1 g.2
  have hg' := Subgroup.mem_prod.1 g'.2
  have key : ∀ k (hk3 : k < 3), (g : Equiv.Perm (Fin N) × Equiv.Perm (Fin N)).1
      (base3[k]'(by rw [base3_length]; exact hk3)) =
        (g' : Equiv.Perm (Fin N) × Equiv.Perm (Fin N)).1
          (base3[k]'(by rw [base3_length]; exact hk3)) ∧
      (g : Equiv.Perm (Fin N) × Equiv.Perm (Fin N)).2
        (base3[k]'(by rw [base3_length]; exact hk3)) =
          (g' : Equiv.Perm (Fin N) × Equiv.Perm (Fin N)).2
            (base3[k]'(by rw [base3_length]; exact hk3)) := by
    intro k hk3
    obtain ⟨a1, a2⟩ := hk k (by rw [base3_length]; exact hk3)
    obtain ⟨b1, b2⟩ := hk' k (by rw [base3_length]; exact hk3)
    exact ⟨Fin.ext (a1.symm.trans b1), Fin.ext (by omega)⟩
  apply Subtype.ext
  apply Prod.ext
  · exact eq_of_three hg.1 hg'.1 (key 0 (by norm_num)).1 (key 1 (by norm_num)).1
      (key 2 (by norm_num)).1
  · exact eq_of_three hg.2 hg'.2 (key 0 (by norm_num)).2 (key 1 (by norm_num)).2
      (key 2 (by norm_num)).2

theorem lifts_length_list :
    localCert.records.map (fun r => r.lifts.length) = [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0] := by
  have h := local_form_cert
  simp only [localFormOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem recK_lifts_length
    {k : ℕ} (hk : k < 12) :
    (recK k).lifts.length = [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0].getD k 0 := by
  have hk' : k < localCert.records.length := by rw [records_length]; exact hk
  have h := congrArg (fun l => l.getD k 0) lifts_length_list
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk'), List.getElem_map] at h
  rw [← h, recK, List.getD_eq_getElem _ _ hk']

theorem lift_record_cases
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    k = 0 ∨ k = 3 ∨ k = 9 ∨ k = 10 := by
  have hlen := recK_lifts_length hk
  have hne : (recK k).lifts.length ≠ 0 := fun h => by
    rw [List.length_eq_zero_iff] at h
    rw [h] at he
    exact absurd he List.not_mem_nil
  rw [hlen] at hne
  interval_cases k <;> simp only [List.getD_cons_succ, List.getD_cons_zero] at hne <;> omega

end CFSG.Sporadic.ONOddCore
