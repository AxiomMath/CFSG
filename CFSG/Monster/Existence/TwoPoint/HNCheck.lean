module

public import CFSG.Monster.Existence.TwoPoint.HNRigid
public import CFSG.Monster.Existence.TwoPoint.HNData
public import Certificates.Data.CFSGNative.Bridge.HNGPL

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

@[expose] def hnLetterW (l : ℕ × Bool) : List Native.Gen :=
  if l.2 then hnWU[l.1]! else hnWV[l.1]!

@[expose] def hnRelW (R : List (ℕ × Bool)) : List Native.Gen :=
  (R.reverse.map hnLetterW).flatten

@[expose] def hnPU : Array (List Native.PGen) := hnWU.map HS.pw

@[expose] def hnPV : Array (List Native.PGen) := hnWV.map HS.pw

@[expose] def hnLetterP (l : ℕ × Bool) : List Native.PGen :=
  if l.2 then hnPU[l.1]! else hnPV[l.1]!

@[expose] def hnRelP (R : List (ℕ × Bool)) : List Native.PGen :=
  (R.reverse.map hnLetterP).flatten

theorem hnWU_size : hnWU.size = 5 := rfl

theorem hnWV_size : hnWV.size = 5 := rfl

theorem hnPU_get {i : ℕ} (hi : i < 5) : hnPU[i]! = HS.pw hnWU[i]! := by
  have h : i < hnWU.size := by rw [hnWU_size]; exact hi
  unfold hnPU
  rw [getElem!_pos (hnWU.map HS.pw) i (by rw [Array.size_map]; exact h), Array.getElem_map,
    getElem!_pos hnWU i h]

theorem hnPV_get {i : ℕ} (hi : i < 5) : hnPV[i]! = HS.pw hnWV[i]! := by
  have h : i < hnWV.size := by rw [hnWV_size]; exact hi
  unfold hnPV
  rw [getElem!_pos (hnWV.map HS.pw) i (by rw [Array.size_map]; exact h), Array.getElem_map,
    getElem!_pos hnWV i h]

theorem hnLetterP_eq {l : ℕ × Bool} (hl : l.1 < 5) : hnLetterP l = HS.pw (hnLetterW l) := by
  unfold hnLetterP hnLetterW
  cases h : l.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hnPV_get hl
  · simp only [↓reduceIte]
    exact hnPU_get hl

theorem hn_pw_flatten (L : List (List Native.Gen)) :
    HS.pw L.flatten = (L.map HS.pw).flatten := by
  unfold HS.pw Native.prepWordG
  exact List.map_flatten ..

theorem hnRelP_eq {R : List (ℕ × Bool)} (hR : ∀ l ∈ R, l.1 < 5) :
    hnRelP R = HS.pw (hnRelW R) := by
  unfold hnRelP hnRelW
  rw [hn_pw_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  have := hR l (List.mem_reverse.1 hl)
  exact hnLetterP_eq this

@[expose] def hnNotTau : Native.Gen → Bool
  | .tau => false
  | _ => true

theorem hnNotTau_spec {g : Native.Gen} (h : hnNotTau g = true) : ¬ g = .tau := by
  cases g <;> simp_all [hnNotTau]

@[expose, noinline] def hnRelCheck (R : List (ℕ × Bool)) : Bool :=
  (hnRelW R).all Native.Gen.validB && R.all (fun l => decide (l.1 < 5)) &&
    (if (hnRelW R).all hnNotTau then checkP2 (hnRelP R) [] else checkP4 (hnRelP R) [])

@[expose] def hnRelsCheck (idx : List ℕ) : Bool := idx.all fun i => hnRelCheck hnRels[i]!

theorem wordLin_hnRelW
    {R : List (ℕ × Bool)} (h : hnRelCheck R = true) :
    wordLin (hnRelW R) = 1 := by
  unfold hnRelCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hR⟩, hc⟩ := h
  have hv' : ((hnRelW R) ++ []).all Native.Gen.validB = true := by
    simpa [List.all_eq_true] using hv
  have hP := hnRelP_eq hR
  split_ifs at hc with ht
  · rw [hP] at hc
    have := wordLin_eq_of_checkP2 (w₁ := hnRelW R) (w₂ := [])
      (fun g hg => hnNotTau_spec (ht g hg)) (fun g hg => absurd hg (by simp))
      hv' hc
    rwa [wordLin_nil] at this
  · rw [hP] at hc
    have := wordLin_eq_of_checkP4 (w₁ := hnRelW R) (w₂ := []) hv' hc
    rwa [wordLin_nil] at this

@[expose, noinline] def hnInvCheck (i : ℕ) : Bool :=
  (hnWU[i]! ++ hnWV[i]!).all Native.Gen.validB && decide (i < 5) &&
    checkP4 (hnPU[i]! ++ hnPV[i]!) []

theorem hn_wordLin_inv
    {i : ℕ} (h : hnInvCheck i = true) :
    wordLin hnWV[i]! * wordLin hnWU[i]! = 1 := by
  unfold hnInvCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hi⟩, hc⟩ := h
  have hv' : ((hnWU[i]! ++ hnWV[i]!) ++ []).all Native.Gen.validB = true := by
    simpa using hv
  have e : hnPU[i]! ++ hnPV[i]! = HS.pw (hnWU[i]! ++ hnWV[i]!) := by
    rw [hnPU_get hi, hnPV_get hi, HS.pw_append]
  rw [e] at hc
  have := wordLin_eq_of_checkP4 (w₁ := hnWU[i]! ++ hnWV[i]!) (w₂ := []) hv' hc
  rwa [wordLin_append, wordLin_nil] at this

@[expose, noinline] def hnAxisFixCheck (pc px : List Native.PGen) : Bool :=
  (Native.evalPrep HS.hsCtx px (Native.evalPrep HS.hsCtx pc HS.axisP)).eqv
    (Native.evalPrep HS.hsCtx pc HS.axisP)

theorem hn_axisFix_sound
    {c x : List Native.Gen} (hc : c.all Native.Gen.validB = true)
    (hx : x.all Native.Gen.validB = true) (h : hnAxisFixCheck (HS.pw c) (HS.pw x) = true) :
    wordLin x (wordLin c aStar) = wordLin c aStar := by
  have := eqv_sound h
  rwa [HS.interp_evalPrep_pw hx, HS.interp_evalPrep_pw hc, HS.interp_axisP] at this

@[expose, noinline] def hnGenFixCheck (c : List Native.Gen) (i : ℕ) : Bool :=
  c.all Native.Gen.validB && hnWU[i]!.all Native.Gen.validB && decide (i < 5) &&
    hnAxisFixCheck (HS.pw c) hnPU[i]!

theorem hn_genFix_sound
    {c : List Native.Gen} {i : ℕ} (h : hnGenFixCheck c i = true) :
    wordLin hnWU[i]! (wordLin c aStar) = wordLin c aStar := by
  unfold hnGenFixCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, hx⟩, hi⟩, hf⟩ := h
  rw [hnPU_get hi] at hf
  exact hn_axisFix_sound hc hx hf

@[expose, noinline] def hnConjCheck (c w : List Native.Gen) : Bool :=
  (hnRhoT ++ c ++ (c ++ w)).all Native.Gen.validB && checkP4 (HS.pw (hnRhoT ++ c)) (HS.pw (c ++ w))

theorem hn_wordLin_conj
    {c w : List Native.Gen} (h : hnConjCheck c w = true) :
    wordLin c * wordLin hnRhoT = wordLin w * wordLin c := by
  unfold hnConjCheck at h
  rw [Bool.and_eq_true] at h
  have := wordLin_eq_of_checkP4 (w₁ := hnRhoT ++ c) (w₂ := c ++ w) (by simpa [List.append_assoc]
    using h.1) h.2
  rwa [wordLin_append, wordLin_append] at this

@[expose] def hnWAB : List Native.Gen := hnWBeta ++ hnWAlpha

@[expose] def hnWAB5 : List Native.Gen := hnWAB ++ hnWAB ++ hnWAB ++ hnWAB ++ hnWAB

@[expose, noinline] def hnOrd5Check : Bool :=
  hnWAB5.all Native.Gen.validB && checkP4 (HS.pw hnWAB5) []

@[expose, noinline] def hnNeABCheck : Bool :=
  hnWAB.all Native.Gen.validB &&
    hnDiffA 0 0 (Native.evalPrep HS.hsCtx (HS.pw hnWAB) HS.axisP) HS.axisP

@[expose, noinline] def hnNeTCheck : Bool :=
  hnWU[4]!.all Native.Gen.validB &&
    hnDiffA 0 0 (Native.evalPrep HS.hsCtx hnPU[4]! HS.axisP) HS.axisP

@[expose, noinline] def hnMiscCheck : Bool :=
  (List.range 5).all hnInvCheck && (List.range 5).all (hnGenFixCheck hnCAlpha) &&
    (List.range 5).all (hnGenFixCheck hnCBeta) && hnNeABCheck && hnNeTCheck

@[expose, noinline] def hnConjOrdCheck : Bool :=
  hnConjCheck hnCAlpha hnWAlpha && hnConjCheck hnCBeta hnWBeta && hnOrd5Check

theorem hn_wordLin_ab_pow_five
    (h : hnOrd5Check = true) : (wordLin hnWAB) ^ 5 = 1 := by
  unfold hnOrd5Check at h
  rw [Bool.and_eq_true] at h
  have := wordLin_eq_of_checkP4 (w₁ := hnWAB5) (w₂ := []) (by simpa using h.1) h.2
  rw [wordLin_nil] at this
  rw [← this]
  simp only [hnWAB5, wordLin_append]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem hn_wordLin_ab_ne_one
    (h : hnNeABCheck = true) : wordLin hnWAB ≠ 1 := by
  unfold hnNeABCheck at h
  rw [Bool.and_eq_true] at h
  exact hn_wordLin_ne_one_of_diffA (i := 0) (j := 0) h.1 h.2

theorem wordLin_hnWU_four_ne_one
    (h : hnNeTCheck = true) : wordLin hnWU[4]! ≠ 1 := by
  unfold hnNeTCheck at h
  rw [Bool.and_eq_true] at h
  have hp : hnPU[4]! = HS.pw hnWU[4]! := hnPU_get (by norm_num)
  rw [hp] at h
  exact hn_wordLin_ne_one_of_diffA (i := 0) (j := 0) h.1 h.2

end CFSG.Monster.Existence
