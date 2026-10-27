module

public import CFSG.GH74.Uniqueness.SU.KI1r4F61L34MInputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import CFSG.Certificates.Kernel.Griess13.SLPTextSound
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import Certificates.Kernel.PermCent.K5138
import all Init.Data.String.Slice
import all Init.Data.String.Search
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups
  CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.L34MT
  CFSG.Certificates.Kernel.PkEnum

namespace Certificates

private theorem dvalC_eq (cs : List Char) (a : Nat) : dvalC cs a = Nat.ofDigitChars 10 cs a := by
  induction cs generalizing a with
  | nil => rw [dvalC, Nat.ofDigitChars_nil]
  | cons c cs ih =>
    rw [dvalC, Nat.ofDigitChars_cons, ih]
    rfl

private theorem toInt!_digits {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) :
    (String.ofList ds).toInt! = (dvalC ds 0 : Int) := by
  have h := CFSG.KS.SporSch.LyTxt.tv_pos hd hne
  unfold CFSG.KS.SporSch.LyTxt.tv String.toInt? at h
  unfold String.toInt! String.Slice.toInt!
  rw [h, dvalC_eq]

private theorem ofList_isEmpty' (p : List Char) : (String.ofList p).isEmpty = p.isEmpty := by
  cases p <;> simp [String.isEmpty_iff]

private theorem splC_eq (c : Char) (cs acc : List Char) :
    splC c cs acc = List.splitOnPPrepend (· == c) cs acc := by
  induction cs generalizing acc with
  | nil => rw [splC, List.splitOnPPrepend_nil]
  | cons d cs ih =>
    rw [splC, List.splitOnPPrepend_cons_eq_ite, ih, ih]
    by_cases h : d = c <;> simp [h]

private theorem splC_splitOn (c : Char) (cs : List Char) : splC c cs [] = cs.splitOn c := by
  rw [splC_eq, List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend]

private theorem parseWords_ofList (cs : List Char) (h : charsOK cs = true) :
    parseWords (String.ofList cs) = wordsC cs := by
  have hc : ∀ x ∈ cs, x.isDigit = true ∨ x = ';' ∨ x = ' ' := by
    intro x hx
    have := List.all_eq_true.1 h x hx
    simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using this
  unfold parseWords wordsC
  simp only [splC_splitOn]
  rw [CFSG.KC.G13.splitOn_semi, List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp_apply]
  rw [CFSG.KC.G13.splitOn_space, List.filterMap_map]
  apply List.filterMap_congr
  intro t ht
  simp only [Function.comp_apply, ofList_isEmpty']
  by_cases he : t.isEmpty = true
  · simp [he]
  · rw [if_neg he, if_neg he]
    have hne : t ≠ [] := fun e => he (by rw [e]; rfl)
    rw [List.splitOn_eq_splitOnP] at hw ht
    have hd : ∀ c ∈ t, c.isDigit = true := by
      intro c hct
      obtain ⟨hcw, hcs⟩ := CFSG.KS.DecLines.mem_splitOnP w t ht c hct
      obtain ⟨hcc, hcsemi⟩ := CFSG.KS.DecLines.mem_splitOnP cs w hw c hcw
      rcases hc c hcc with h1 | h1 | h1
      · exact h1
      · subst h1
        simp at hcsemi
      · subst h1
        simp at hcs
    rw [toInt!_digits hd hne]

private theorem cOf_one' : cOf (1 : Equiv.Perm (Fin 42)) = 1 :=
  ev_injective (by rw [ev_cOf, ev_one])

private theorem ev_evCodesC (S : List (Equiv.Perm (Fin 42))) (w : List ℤ) :
    ev (evCodesC (S.map cOf) w) = evalCodes S w := by
  induction w with
  | nil => rw [evCodesC, evalCodes, ev_one]
  | cons z w ih =>
    rw [evCodesC, evalCodes, ev_mul, ih, ← cOf_one', List.getD_map, List.getD_map]
    split
    · rw [ev_cOf]
    · rw [ev_inv, ev_cOf]

private theorem cl_eq (r : Equiv.Perm (Fin 42)) (ws : List (List ℤ)) (cs : List Char)
    (h : ws = wordsC cs) : (clList r ws).map cOf = clC r cs := by
  rw [clC, clList, ← h, List.map_map]
  refine List.map_congr_left fun w _ => ev_injective ?_
  rw [Function.comp_apply, ev_cOf, tab_eq, ev_mul, ev_mul, ev_inv, ev_evCodesC, ev_cOf]

private theorem cover_eq : ((elemsT QA).all fun g => !decide (g ^ 2 = 1) || decide (g = 1) ||
    cl1.contains g || cl2.contains g || cl3.contains g || cl4.contains g) =
      coverC (clC rep1 W1.chars) (clC rep2 W2.chars) (clC rep3 W3.chars) (clC rep4 W4.chars) := by
  have h1 : cl1.map cOf = clC rep1 W1.chars := cl_eq _ _ _ (by
    rw [words1.eq_1, W1.eq, parseWords_ofList _ kChars.1])
  have h2 : cl2.map cOf = clC rep2 W2.chars := cl_eq _ _ _ (by
    rw [words2.eq_1, W2.eq, parseWords_ofList _ kChars.2.1])
  have h3 : cl3.map cOf = clC rep3 W3.chars := cl_eq _ _ _ (by
    rw [words3.eq_1, W3.eq, parseWords_ofList _ kChars.2.2.1])
  have h4 : cl4.map cOf = clC rep4 W4.chars := cl_eq _ _ _ (by
    rw [words4.eq_1, W4.eq, parseWords_ofList _ kChars.2.2.2])
  rw [coverC.eq_1, elemsT_eq_elemsC, List.all_map]
  refine congrArg (List.all (elemsC QA)) (funext fun g => ?_)
  simp only [Function.comp_apply, ev_pow', one_eq_ev, decide_ev_eq, pow_fast, contains_ev,
    ← h1, ← h2, ← h3, ← h4]

private theorem cent_eq' : ((elemsT QP).filter fun g => decide (g * rep4 = rep4 * g)).length =
    ((elemsC QP).filter fun g => eq22C g (cOf rep4) (cOf rep4) g).length := by
  conv_lhs => rw [eq_ev_cOf rep4, elemsT_eq_elemsC]
  simp only [List.filter_map, List.length_map, Function.comp_def, ev_mul', decide_ev_eq,
    comm_fast]

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Uniqueness in
open CFSG.GH74.Uniqueness.SU in
open CFSG.GH74.Uniqueness.SU.K in
open CFSG.GH74.Uniqueness.SU.K.R4 in
open CFSG.GH74.Uniqueness.SU.K.R4.L34M in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 in
theorem certificate5138 : (((elemsT QA).all fun g => !decide (g ^ 2 = 1) || decide (g = 1) || cl1.contains g ||
    cl2.contains g || cl3.contains g || cl4.contains g) = true)
    ∧ (9 ∣ Nat.card ↥(QP.originalSubgroup ⊓
    Subgroup.centralizer ({rep4} : Set (Equiv.Perm (Fin 42)))))
    ∧ (QP.sift e4u0 0 = true ∧ QP.sift e4v0 0 = true ∧
    (decide (e4u0 ≠ 1) && decide (e4v0 ≠ 1) && decide (e4u0 ≠ e4v0) && decide (e4u0 ^ 2 = 1) &&
      decide (e4v0 ^ 2 = 1) && decide (e4u0 * e4v0 = e4v0 * e4u0) && decide (1 * e4u0 = e4u0 * 1) &&
      decide (1 * e4v0 = e4v0 * 1)) = true)
    ∧ (QP.sift e4u1 0 = true ∧ QP.sift e4v1 0 = true ∧
    (decide (e4u1 ≠ 1) && decide (e4v1 ≠ 1) && decide (e4u1 ≠ e4v1) && decide (e4u1 ^ 2 = 1) &&
      decide (e4v1 ^ 2 = 1) && decide (e4u1 * e4v1 = e4v1 * e4u1) && decide (rep1 * e4u1 = e4u1 * rep1) &&
      decide (rep1 * e4v1 = e4v1 * rep1)) = true)
    ∧ (QP.sift e4u2 0 = true ∧ QP.sift e4v2 0 = true ∧
    (decide (e4u2 ≠ 1) && decide (e4v2 ≠ 1) && decide (e4u2 ≠ e4v2) && decide (e4u2 ^ 2 = 1) &&
      decide (e4v2 ^ 2 = 1) && decide (e4u2 * e4v2 = e4v2 * e4u2) && decide (rep2 * e4u2 = e4u2 * rep2) &&
      decide (rep2 * e4v2 = e4v2 * rep2)) = true)
    ∧ (QP.sift e4u3 0 = true ∧ QP.sift e4v3 0 = true ∧
    (decide (e4u3 ≠ 1) && decide (e4v3 ≠ 1) && decide (e4u3 ≠ e4v3) && decide (e4u3 ^ 2 = 1) &&
      decide (e4v3 ^ 2 = 1) && decide (e4u3 * e4v3 = e4v3 * e4u3) && decide (rep3 * e4u3 = e4u3 * rep3) &&
      decide (rep3 * e4v3 = e4v3 * rep3)) = true) := by
  have hQP : ValidSchreier QP := check_certificate_of _ _ _ _ _ kQP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cover_eq]
    exact kCover
  · rw [card_inf_centralizer QP hQP rep4, cent_eq']
    exact Nat.dvd_of_mod_eq_zero kCent
  · simp only [sift_eq_siftP]
    exact kE0
  · simp only [sift_eq_siftP]
    exact kE1
  · simp only [sift_eq_siftP]
    exact kE2
  · simp only [sift_eq_siftP]
    exact kE3

end Certificates
