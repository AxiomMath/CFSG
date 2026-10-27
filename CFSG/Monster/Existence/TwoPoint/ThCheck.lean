module

public import CFSG.Monster.Existence.TwoPoint.HNRigid
public import CFSG.Monster.Existence.TwoPoint.ThData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short

@[expose] def thLetterW (l : ℕ × Bool) : List Native.Gen :=
  if l.2 then thWU[l.1]! else thWV[l.1]!

@[expose] def thRelW (R : List (ℕ × Bool)) : List Native.Gen :=
  (R.reverse.map thLetterW).flatten

@[expose] def thPU : Array (List Native.PGen) := thWU.map HS.pw

@[expose] def thPV : Array (List Native.PGen) := thWV.map HS.pw

@[expose] def thLetterP (l : ℕ × Bool) : List Native.PGen :=
  if l.2 then thPU[l.1]! else thPV[l.1]!

@[expose] def thRelP (R : List (ℕ × Bool)) : List Native.PGen :=
  (R.reverse.map thLetterP).flatten

theorem thWU_size : thWU.size = 8 := rfl

theorem thWV_size : thWV.size = 8 := rfl

theorem thPU_get {i : ℕ} (hi : i < 8) : thPU[i]! = HS.pw thWU[i]! := by
  have h : i < thWU.size := by rw [thWU_size]; exact hi
  unfold thPU
  rw [getElem!_pos (thWU.map HS.pw) i (by rw [Array.size_map]; exact h), Array.getElem_map,
    getElem!_pos thWU i h]

theorem thPV_get {i : ℕ} (hi : i < 8) : thPV[i]! = HS.pw thWV[i]! := by
  have h : i < thWV.size := by rw [thWV_size]; exact hi
  unfold thPV
  rw [getElem!_pos (thWV.map HS.pw) i (by rw [Array.size_map]; exact h), Array.getElem_map,
    getElem!_pos thWV i h]

theorem thLetterP_eq {l : ℕ × Bool} (hl : l.1 < 8) : thLetterP l = HS.pw (thLetterW l) := by
  unfold thLetterP thLetterW
  cases h : l.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact thPV_get hl
  · simp only [↓reduceIte]
    exact thPU_get hl

theorem th_pw_flatten (L : List (List Native.Gen)) :
    HS.pw L.flatten = (L.map HS.pw).flatten := by
  unfold HS.pw Native.prepWordG
  exact List.map_flatten ..

theorem thRelP_eq {R : List (ℕ × Bool)} (hR : ∀ l ∈ R, l.1 < 8) :
    thRelP R = HS.pw (thRelW R) := by
  unfold thRelP thRelW
  rw [th_pw_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  have := hR l (List.mem_reverse.1 hl)
  exact thLetterP_eq this

@[expose] def thNotTau : Native.Gen → Bool
  | .tau => false
  | _ => true

theorem thNotTau_spec {g : Native.Gen} (h : thNotTau g = true) : ¬ g = .tau := by
  cases g <;> simp_all [thNotTau]

@[expose, noinline] def thIdP (noTau : Bool) (p₁ p₂ : List Native.PGen) : Bool :=
  if noTau then checkP2 p₁ p₂ else checkP4 p₁ p₂

@[expose, noinline] def thIdCheck (w₁ w₂ : List Native.Gen) : Bool :=
  (w₁ ++ w₂).all Native.Gen.validB && thIdP ((w₁ ++ w₂).all thNotTau) (HS.pw w₁) (HS.pw w₂)

theorem wordLin_eq_of_thIdP
    {w₁ w₂ : List Native.Gen} (hv : (w₁ ++ w₂).all Native.Gen.validB = true)
    (h : thIdP ((w₁ ++ w₂).all thNotTau) (HS.pw w₁) (HS.pw w₂) = true) :
    wordLin w₁ = wordLin w₂ := by
  unfold thIdP at h
  split_ifs at h with ht
  · simp only [List.all_append, Bool.and_eq_true, List.all_eq_true] at ht
    exact wordLin_eq_of_checkP2 (fun g hg => thNotTau_spec (ht.1 g hg))
      (fun g hg => thNotTau_spec (ht.2 g hg)) hv h
  · exact wordLin_eq_of_checkP4 hv h

theorem wordLin_eq_of_thIdCheck
    {w₁ w₂ : List Native.Gen} (h : thIdCheck w₁ w₂ = true) :
    wordLin w₁ = wordLin w₂ := by
  unfold thIdCheck at h
  rw [Bool.and_eq_true] at h
  exact wordLin_eq_of_thIdP h.1 h.2

@[expose, noinline] def thRelCheck (R : List (ℕ × Bool)) : Bool :=
  (thRelW R).all Native.Gen.validB && R.all (fun l => decide (l.1 < 8)) &&
    thIdP ((thRelW R).all thNotTau) (thRelP R) []

@[expose] def thRelsCheck (rels : List (List (ℕ × Bool))) (idx : List ℕ) : Bool :=
  idx.all fun i => thRelCheck rels[i]!

theorem wordLin_thRelW
    {R : List (ℕ × Bool)} (h : thRelCheck R = true) :
    wordLin (thRelW R) = 1 := by
  unfold thRelCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hR⟩, hc⟩ := h
  have hv' : ((thRelW R) ++ []).all Native.Gen.validB = true := by
    simpa [List.all_eq_true] using hv
  have hP := thRelP_eq hR
  rw [hP] at hc
  have h2 : thIdP (((thRelW R) ++ []).all thNotTau) (HS.pw (thRelW R)) (HS.pw []) = true := by
    simpa [List.all_eq_true, HS.pw, Native.prepWordG] using hc
  have := wordLin_eq_of_thIdP hv' h2
  rwa [wordLin_nil] at this

@[expose, noinline] def thInvCheck (i : ℕ) : Bool :=
  (thWU[i]! ++ thWV[i]!).all Native.Gen.validB && decide (i < 8) &&
    thIdP ((thWU[i]! ++ thWV[i]!).all thNotTau) (thPU[i]! ++ thPV[i]!) []

theorem th_wordLin_inv
    {i : ℕ} (h : thInvCheck i = true) :
    wordLin thWV[i]! * wordLin thWU[i]! = 1 := by
  unfold thInvCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hi⟩, hc⟩ := h
  have hv' : ((thWU[i]! ++ thWV[i]!) ++ []).all Native.Gen.validB = true := by
    simpa using hv
  have e : thPU[i]! ++ thPV[i]! = HS.pw (thWU[i]! ++ thWV[i]!) := by
    rw [thPU_get hi, thPV_get hi, HS.pw_append]
  rw [e] at hc
  have h2 : thIdP (((thWU[i]! ++ thWV[i]!) ++ []).all thNotTau) (HS.pw (thWU[i]! ++ thWV[i]!))
      (HS.pw []) = true := by
    simpa [HS.pw, Native.prepWordG] using hc
  have := wordLin_eq_of_thIdP hv' h2
  rwa [wordLin_append, wordLin_nil] at this

@[expose, noinline] def thCommCheck (w : List Native.Gen) (i : ℕ) : Bool :=
  decide (i < 8) && thIdCheck (w ++ thWU[i]!) (thWU[i]! ++ w)

theorem th_comm_sound
    {w : List Native.Gen} {i : ℕ} (h : thCommCheck w i = true) :
    wordLin thWU[i]! * wordLin w = wordLin w * wordLin thWU[i]! := by
  unfold thCommCheck at h
  rw [Bool.and_eq_true] at h
  have := wordLin_eq_of_thIdCheck h.2
  rwa [wordLin_append, wordLin_append] at this

@[expose, noinline] def thConjCheck (c w : List Native.Gen) : Bool :=
  thIdCheck (thRhoT ++ c) (c ++ w)

theorem th_wordLin_conj
    {c w : List Native.Gen} (h : thConjCheck c w = true) :
    wordLin c * wordLin thRhoT = wordLin w * wordLin c := by
  have := wordLin_eq_of_thIdCheck h
  rwa [wordLin_append, wordLin_append] at this

@[expose] def thWAB : List Native.Gen := thWBeta ++ thWAlpha

@[expose] def thWAB3 : List Native.Gen := thWAB ++ thWAB ++ thWAB

@[expose, noinline] def thOrd3Check : Bool := thIdCheck thWAB3 []

theorem th_wordLin_ab_pow_three
    (h : thOrd3Check = true) : (wordLin thWAB) ^ 3 = 1 := by
  have := wordLin_eq_of_thIdCheck h
  rw [wordLin_nil] at this
  rw [← this]
  simp only [thWAB3, wordLin_append]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

@[expose, noinline] def thNeABCheck : Bool :=
  thWAB.all Native.Gen.validB &&
    hnDiffA 0 0 (Native.evalPrep HS.hsCtx (HS.pw thWAB) HS.axisP) HS.axisP

theorem th_wordLin_ab_ne_one
    (h : thNeABCheck = true) : wordLin thWAB ≠ 1 := by
  unfold thNeABCheck at h
  rw [Bool.and_eq_true] at h
  exact hn_wordLin_ne_one_of_diffA (i := 0) (j := 0) h.1 h.2

@[expose, noinline] def thThreeCCheck (wT : List Native.Gen) : Bool :=
  thIdCheck (wT ++ thWG) (thWG ++ thWAB)

theorem th_threeC_sound
    {wT : List Native.Gen} (h : thThreeCCheck wT = true) :
    wordLin thWG * wordLin wT = wordLin thWAB * wordLin thWG := by
  have := wordLin_eq_of_thIdCheck h
  rwa [wordLin_append, wordLin_append] at this

@[expose] def thWS7 : List Native.Gen :=
  thWU[5]! ++ thWU[5]! ++ thWU[5]! ++ thWU[5]! ++ thWU[5]! ++ thWU[5]! ++ thWU[5]!

@[expose, noinline] def thOrd7Check : Bool := thIdCheck thWS7 []

theorem th_wordLin_s_pow_seven
    (h : thOrd7Check = true) : (wordLin thWU[5]!) ^ 7 = 1 := by
  have := wordLin_eq_of_thIdCheck h
  rw [wordLin_nil] at this
  rw [← this]
  simp only [thWS7, wordLin_append]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

@[expose, noinline] def thNeSCheck : Bool :=
  thWU[5]!.all Native.Gen.validB &&
    hnDiffA 0 0 (Native.evalPrep HS.hsCtx thPU[5]! HS.axisP) HS.axisP

theorem th_wordLin_s_ne_one
    (h : thNeSCheck = true) : wordLin thWU[5]! ≠ 1 := by
  unfold thNeSCheck at h
  rw [Bool.and_eq_true] at h
  have hp : thPU[5]! = HS.pw thWU[5]! := thPU_get (by norm_num)
  rw [hp] at h
  exact hn_wordLin_ne_one_of_diffA (i := 0) (j := 0) h.1 h.2

@[expose] def thVisCheck : Bool :=
  thWAlpha.all Native.Gen.isVis && thWBeta.all Native.Gen.isVis && thWU[5]!.all Native.Gen.isVis

@[expose, noinline] def thMiscCheck : Bool :=
  (List.range 8).all thInvCheck && thOrd3Check && thNeABCheck && thOrd7Check && thNeSCheck &&
    thVisCheck

@[expose, noinline] def thCommAlphaCheck : Bool := (List.range 8).all (thCommCheck thWAlpha)

@[expose, noinline] def thCommBetaCheck : Bool := (List.range 8).all (thCommCheck thWBeta)

@[expose, noinline] def thConjOrdCheck : Bool :=
  thConjCheck thCAlpha thWAlpha && thConjCheck thCBeta thWBeta

end CFSG.Monster.Existence
