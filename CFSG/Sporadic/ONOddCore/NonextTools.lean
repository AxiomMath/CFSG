module

public import CFSG.Sporadic.ONOddCore.NonextData
public import CFSG.Sporadic.ONOddCore.NonextCheck
public import CFSG.Sporadic.ONOddCore.LiftAut
public import CFSG.Sporadic.Schreier.ONTwoCentralizer

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

theorem lettersOK_iff {k : ℕ} {w : List ℕ} : lettersOK k w = true ↔ ∀ l ∈ w, 1 ≤ l ∧ l ≤ k := by
  simp [lettersOK, List.all_eq_true]

theorem prep_conjArr {y yi x : Array ℕ} {Y X : Equiv.Perm (Fin N)} (hy : PRep N y Y)
    (hyi : PRep N yi Y⁻¹) (hx : PRep N x X) : PRep N (conjArr y yi x) (Y * X * Y⁻¹) := by
  have := prep_pcomp hy (prep_pcomp hx hyi)
  rwa [← mul_assoc] at this

theorem prep_cConj
    {x : Array ℕ} {X : Equiv.Perm (Fin N)} (hx : PRep N x X) :
    PRep N (cConj x) (onc * X * onc⁻¹) :=
  prep_conjArr prep_onc prep_onc_inv hx

theorem prep_inv_pinvCand {x : Array ℕ} {X : Equiv.Perm (Fin N)} (hx : PRep N x X)
    (h : pisInv nPts x (pinvCand nPts x) = true) : PRep N (pinvCand nPts x) X⁻¹ :=
  prep_inv_of_pisInv hx h

theorem getD_eq_getElem! {A : Array (Array ℕ)} {i : ℕ} (hi : i < A.size) (d : Array ℕ) :
    A.getD i d = A[i]! := by
  rw [Array.getD_eq_getD_getElem?, getElem!_pos A i hi, getElem?_pos A i hi, Option.getD_some]

theorem prep_posArr_six {A B : Array (Array ℕ)} {GA GB : List (Equiv.Perm (Fin N))}
    (hA : A.size = 3) (hB : B.size = 3) (hGA : GA.length = 3) (hGB : GB.length = 3)
    (h1 : ∀ i < 3, PRep N A[i]! (GA.getD i 1)) (h2 : ∀ i < 3, PRep N B[i]! (GB.getD i 1))
    {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) :
    PRep N (posArr nPts (A ++ B) w) (evalPos (GA ++ GB) w) := by
  refine prep_posArr (fun l hl1 hl2 => ?_) w (fun l hl => ⟨(hw l hl).1, by
    rw [List.length_append, hGA, hGB]; exact (hw l hl).2⟩)
  rw [List.length_append, hGA, hGB] at hl2
  have hsz : (A ++ B).size = 6 := by rw [Array.size_append, hA, hB]
  rw [getD_eq_getElem! (by rw [hsz]; omega)]
  by_cases hl : l - 1 < 3
  · rw [getElem!_pos _ _ (by rw [hsz]; omega), Array.getElem_append_left (by rw [hA]; exact hl),
      ← getElem!_pos A _ (by rw [hA]; exact hl),
      List.getD_append _ _ _ _ (by rw [hGA]; exact hl)]
    exact h1 _ hl
  · have hl' : l - 1 - 3 < 3 := by omega
    have e : ∀ (j : ℕ) (hj : j < B.size), j = l - 1 - 3 → B[j] = B[l - 1 - 3]! := by
      rintro j hj rfl
      rw [getElem!_pos B _ hj]
    rw [getElem!_pos _ _ (by rw [hsz]; omega), Array.getElem_append_right (by rw [hA]; omega),
      e _ _ (by rw [hA]), List.getD_append_right _ _ _ _ (by rw [hGA]; omega), hGA]
    exact h2 _ hl'

theorem nonext_facts :
    auxOK (wordArrs Data.MWords) nonextWords = true ∧
      lettersOK 6 nonextCert.relationWord = true ∧
      peq nPts (posArr nPts (ambArrs (wordArrs Data.MWords)) nonextCert.relationWord)
        (pid nPts) = true ∧
      (∀ x ∈ nonextCert.excluded, exclOK (wordArrs Data.MWords) flatLifts nonextWords
        nonextCert.relationWord x = true) ∧
      ∀ y ∈ nonextCert.inner, innerOK (wordArrs Data.MWords) flatLifts y = true := by
  have h := nonext_cert
  simp only [nonextOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem aux_facts :
    (∀ l ∈ nonextWords.tWord, 1 ≤ l ∧ l ≤ 3) ∧
      peq nPts (posArr nPts (wordArrs Data.MWords) nonextWords.tWord) tArr = true ∧
      (∀ l ∈ nonextWords.vWord, 1 ≤ l ∧ l ≤ 3) ∧
      peq nPts (posArr nPts (wordArrs Data.MWords) nonextWords.vWord) vArr = true ∧
      ∀ i < 4, (∀ l ∈ nonextWords.dWords.getD i [], 1 ≤ l ∧ l ≤ 3) ∧
        (∀ l ∈ nonextWords.dcWords.getD i [], 1 ≤ l ∧ l ≤ 3) ∧
        peq nPts (posArr nPts (wordArrs Data.MWords) (nonextWords.dWords.getD i []))
          (wordArrs Data.intersectionWords)[i]! = true ∧
        peq nPts (posArr nPts (wordArrs Data.MWords) (nonextWords.dcWords.getD i []))
          dConj[i]! = true := by
  have h := nonext_facts.1
  simp only [auxOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨lettersOK_iff.1 h1, h2, lettersOK_iff.1 h3, h4, fun i hi => ?_⟩
  obtain ⟨⟨⟨h6, h7⟩, h8⟩, h9⟩ := h5 i hi
  exact ⟨lettersOK_iff.1 h6, lettersOK_iff.1 h7, h8, h9⟩

@[expose] def tM :
    onM := ⟨ont, ont_mem_M⟩

theorem evalPos_tWord :
    evalPos hGens nonextWords.tWord = tM :=
  Subtype.ext (eq_of_peq (prep_posArr_h aux_facts.1) prep_t aux_facts.2.1)

theorem evalPos_vWord :
    evalPos hGens nonextWords.vWord = vM :=
  Subtype.ext (eq_of_peq (prep_posArr_h aux_facts.2.2.1) CFSG.ONSchreier.prep_v
    aux_facts.2.2.2.1)

@[expose] def eM
    {i : ℕ} (hi : i < 4) : onM :=
  ⟨onDgens[i]'(by rw [onDgens_length]; exact hi), onDgens_mem_M _⟩

@[expose] def ceM
    {i : ℕ} (hi : i < 4) : onM :=
  ⟨onc⁻¹ * onDgens[i]'(by rw [onDgens_length]; exact hi) * onc, dConj_mem_M _⟩

theorem evalPos_dWord
    {i : ℕ} (hi : i < 4) : evalPos hGens (nonextWords.dWords.getD i []) = eM hi :=
  Subtype.ext (eq_of_peq (prep_posArr_h (aux_facts.2.2.2.2 i hi).1) (prep_onDgens i _)
    (aux_facts.2.2.2.2 i hi).2.2.1)

theorem evalPos_dcWord
    {i : ℕ} (hi : i < 4) :
    evalPos hGens (nonextWords.dcWords.getD i []) = ceM hi :=
  Subtype.ext (eq_of_peq (prep_posArr_h (aux_facts.2.2.2.2 i hi).2.1) (prep_dConj _)
    (aux_facts.2.2.2.2 i hi).2.2.2)

theorem getElem!_map_arr {A : Array (Array ℕ)} {f : Array ℕ → Array ℕ} {i : ℕ}
    (hi : i < A.size) : (A.map f)[i]! = f A[i]! := by
  rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_map, getElem!_pos A i hi]

theorem prep_ambArrs
    {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) :
    PRep N (posArr nPts (ambArrs (wordArrs Data.MWords)) w) (evalPos ambGens w) := by
  have hsplit : ambGens = [(mGen 0 : Equiv.Perm (Fin N)), mGen 1, mGen 2] ++
      [onc * mGen 0 * onc⁻¹, onc * mGen 1 * onc⁻¹, onc * mGen 2 * onc⁻¹] := rfl
  rw [hsplit, ambArrs]
  refine prep_posArr_six hA_size (by rw [Array.size_map, hA_size]) rfl rfl (fun i hi => ?_)
    (fun i hi => ?_) hw
  · interval_cases i
    · exact prep_hA (i := 0) (by norm_num)
    · exact prep_hA (i := 1) (by norm_num)
    · exact prep_hA (i := 2) (by norm_num)
  · rw [getElem!_map_arr (by rw [hA_size]; exact hi)]
    interval_cases i
    · exact prep_cConj (prep_hA (i := 0) (by norm_num))
    · exact prep_cConj (prep_hA (i := 1) (by norm_num))
    · exact prep_cConj (prep_hA (i := 2) (by norm_num))

theorem evalPos_relation :
    evalPos ambGens nonextCert.relationWord = 1 :=
  eq_of_peq (prep_ambArrs (lettersOK_iff.1 nonext_facts.2.1)) prep_pid nonext_facts.2.2.1

theorem flatLifts_mem
    {r : ℕ} (hr : r < 16) :
    ∃ k < 12, flatLifts.getD r default ∈ (recK k).lifts := by
  have hmem : flatLifts.getD r default ∈ flatLifts :=
    getD_mem (by rw [flatLifts_length]; exact hr) _
  rw [flatLifts, List.mem_flatMap] at hmem
  obtain ⟨rec, hrec, he⟩ := hmem
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hrec
  have hk12 : k < 12 := by rwa [records_length] at hk
  refine ⟨k, hk12, ?_⟩
  rw [recK, List.getD_eq_getElem _ _ hk]
  exact he

theorem prep_lift_word
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts)
    {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) :
    PRep N (posArr nPts (liftArrs (wordArrs Data.MWords) e) w)
      ((liftAut hk he (evalPos hGens w) : onM) : Equiv.Perm (Fin N)) := by
  obtain ⟨hl, -, -⟩ := lift_form hk he
  rw [liftAut_apply, map_evalPos, hGens_map_liftHom hk he]
  have hc : ((evalPos (liftImgs e) w : onM) : Equiv.Perm (Fin N)) =
      evalPos ((liftImgs e).map onM.subtype) w := map_evalPos onM.subtype _ w
  rw [hc]
  refine prep_posArr (fun l h1 h2 => ?_) w (fun l hl' => ⟨(hw l hl').1, by
    rw [List.length_map, liftImgs, List.length_map, hl]; exact (hw l hl').2⟩)
  rw [List.length_map, liftImgs, List.length_map, hl] at h2
  have hl3 : l - 1 < 3 := by omega
  rw [getD_eq_getElem! (by simp [liftArrs, hl]; exact hl3), getD_map_subtype]
  have e2 : (liftImgs e).getD (l - 1) 1 = liftImg e (l - 1) := by
    rw [liftImgs, List.getD_eq_getElem _ _ (by rw [List.length_map, hl]; exact hl3),
      List.getElem_map, liftImg, List.getD_eq_getElem _ _ (by rw [hl]; exact hl3)]
  rw [e2]
  exact (prep_liftArrs hk he hl3).1

theorem prep_lift_gen
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) {i : ℕ}
    (hi : i < 3) :
    PRep N (liftArrs (wordArrs Data.MWords) e)[i]!
      ((liftAut hk he (hGen i) : onM) : Equiv.Perm (Fin N)) := by
  rw [liftAut_apply, liftHom_gen hk he hi]
  exact (prep_liftArrs hk he hi).1

theorem liftArrs_size
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    (liftArrs (wordArrs Data.MWords) e).size = 3 := by
  obtain ⟨hl, -, -⟩ := lift_form hk he
  simp [liftArrs, hl]

end CFSG.Sporadic.ONOddCore
