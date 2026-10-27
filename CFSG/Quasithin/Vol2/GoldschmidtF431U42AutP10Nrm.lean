module

public import Certificates.Data.H13.U42AutP10Lists
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Cox
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7A

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def p10fL : PL :=
  [0, 1, 2, 12, 14, 13, 9, 11, 10, 6, 8, 7, 3, 5, 4, 15, 16, 22, 19, 18, 24, 21, 17, 23, 20, 25, 30,
   27, 33, 29, 26, 32, 31, 28, 34, 35, 44, 41, 38, 43, 40, 37, 42, 39, 36]

@[expose] def p10eSymL : List PL :=
  [[35, 15, 25, 14, 12, 13, 6, 7, 8, 9, 10, 11, 4, 5, 3, 1, 42, 17, 31, 32, 37, 21, 22, 27, 41, 2,
    39, 23, 28, 29, 43, 18, 19, 33, 38, 0, 36, 20, 34, 26, 40, 24, 16, 30, 44],
   [0, 21, 23, 3, 28, 37, 6, 32, 39, 9, 43, 31, 12, 41, 33, 15, 16, 17, 18, 19, 24, 1, 22, 2, 20,
    34, 26, 38, 4, 42, 30, 11, 7, 14, 25, 40, 36, 5, 27, 8, 35, 13, 29, 10, 44],
   [16, 1, 23, 30, 39, 5, 44, 7, 28, 36, 33, 11, 26, 13, 43, 15, 0, 22, 18, 19, 20, 21, 17, 2, 24,
    27, 12, 25, 8, 40, 3, 31, 32, 10, 38, 42, 9, 37, 34, 4, 29, 41, 35, 14, 6],
   [15, 35, 25, 3, 4, 5, 9, 10, 11, 6, 7, 8, 12, 13, 14, 0, 16, 36, 26, 30, 20, 40, 44, 34, 24, 2,
    18, 38, 28, 29, 19, 39, 43, 33, 23, 1, 17, 37, 27, 31, 21, 41, 42, 32, 22],
   [16, 21, 2, 44, 4, 32, 30, 37, 8, 26, 10, 41, 36, 31, 14, 15, 0, 17, 19, 18, 20, 1, 22, 23, 24,
    29, 9, 40, 28, 25, 6, 13, 5, 33, 42, 38, 12, 7, 35, 39, 27, 11, 34, 43, 3],
   [0, 1, 2, 12, 14, 13, 9, 11, 10, 6, 8, 7, 3, 5, 4, 15, 16, 22, 19, 18, 24, 21, 17, 23, 20, 25,
    30, 27, 33, 29, 26, 32, 31, 28, 34, 35, 44, 41, 38, 43, 40, 37, 42, 39, 36]]

theorem p10_lits_check : p10fL = fhatL ∧ p10eSymL = [p10sL.getD 0 idL, p10sL.getD 2 idL,
    p10sL.getD 4 idL, p10sL.getD 5 idL, evalSL [3, 1, 2, 3, 4, 3, 1, 2, 3], fhatL] := by
  decide +kernel

@[expose] def p10eSymA (k : ℕ) : Ah := [p10sA 0, p10sA 2, p10sA 4, p10sA 5, p10tA, fhatA].getD k 1

@[expose] def evalEL (w : List ℕ) : PL := w.foldr (fun k acc => comp (p10eSymL.getD k idL) acc) idL

@[expose] def aE (w : List ℕ) : Ah := (w.map p10eSymA).prod

@[expose] def parE (w : List ℕ) : ℕ := (w.filter fun k => k < 5).length % 2

@[expose] def p10Kw : List (List ℕ) :=
  [[],
   [1],
   [2],
   [3],
   [4],
   [5],
   [1, 2],
   [1, 3],
   [1, 4],
   [1, 5],
   [2, 3],
   [2, 4],
   [2, 5],
   [3, 2],
   [3, 4],
   [3, 5],
   [4, 3],
   [4, 5],
   [1, 2, 3],
   [1, 2, 4],
   [1, 2, 5],
   [1, 3, 2],
   [1, 3, 4],
   [1, 3, 5],
   [1, 4, 3],
   [1, 4, 5],
   [2, 3, 2],
   [2, 3, 4],
   [2, 3, 5],
   [2, 4, 3],
   [2, 4, 5],
   [3, 2, 4],
   [3, 2, 5],
   [3, 4, 3],
   [3, 4, 5],
   [4, 3, 2],
   [4, 3, 5],
   [1, 2, 3, 2],
   [1, 2, 3, 4],
   [1, 2, 3, 5],
   [1, 2, 4, 3],
   [1, 2, 4, 5],
   [1, 3, 2, 4],
   [1, 3, 2, 5],
   [1, 3, 4, 3],
   [1, 3, 4, 5],
   [1, 4, 3, 2],
   [1, 4, 3, 5],
   [2, 3, 2, 4],
   [2, 3, 2, 5],
   [2, 3, 4, 3],
   [2, 3, 4, 5],
   [2, 4, 3, 2],
   [2, 4, 3, 5],
   [3, 2, 4, 3],
   [3, 2, 4, 5],
   [3, 4, 3, 2],
   [3, 4, 3, 5],
   [4, 3, 2, 5],
   [1, 2, 3, 2, 4],
   [1, 2, 3, 2, 5],
   [1, 2, 3, 4, 3],
   [1, 2, 3, 4, 5],
   [1, 2, 4, 3, 2],
   [1, 2, 4, 3, 5],
   [1, 3, 2, 4, 3],
   [1, 3, 2, 4, 5],
   [1, 3, 4, 3, 2],
   [1, 3, 4, 3, 5],
   [1, 4, 3, 2, 5],
   [2, 3, 2, 4, 3],
   [2, 3, 2, 4, 5],
   [2, 3, 4, 3, 2],
   [2, 3, 4, 3, 5],
   [2, 4, 3, 2, 5],
   [3, 2, 4, 3, 2],
   [3, 2, 4, 3, 5],
   [3, 4, 3, 2, 5],
   [1, 2, 3, 2, 4, 3],
   [1, 2, 3, 2, 4, 5],
   [1, 2, 3, 4, 3, 2],
   [1, 2, 3, 4, 3, 5],
   [1, 2, 4, 3, 2, 5],
   [1, 3, 2, 4, 3, 2],
   [1, 3, 2, 4, 3, 5],
   [1, 3, 4, 3, 2, 5],
   [2, 3, 2, 4, 3, 2],
   [2, 3, 2, 4, 3, 5],
   [2, 3, 4, 3, 2, 5],
   [3, 2, 4, 3, 2, 5],
   [1, 2, 3, 2, 4, 3, 2],
   [1, 2, 3, 2, 4, 3, 5],
   [1, 2, 3, 4, 3, 2, 5],
   [1, 3, 2, 4, 3, 2, 5],
   [2, 3, 2, 4, 3, 2, 5],
   [1, 2, 3, 2, 4, 3, 2, 5]]

@[expose] def p10Kl : List PL := p10KlLit

theorem p10Kl_eq : p10Kl = p10Kw.map evalEL := by decide +kernel

@[expose] def p10Kp : List ℕ := p10Kw.map parE

@[expose] def phiL (l : PL) : PL :=
  if p10Kp.getD (p10Kl.idxOf l) 0 = 1 then comp l p10fL else l

@[expose] def p10hL : PL :=
  [15, 3, 9, 34, 31, 28, 40, 37, 43, 35, 10, 5, 25, 4, 11, 16, 0, 27, 29, 42, 20, 12, 38, 6, 24, 19,
   2, 30, 32, 36, 23, 13, 41, 7, 18, 22, 1, 33, 26, 39, 17, 14, 44, 8, 21]

@[expose] def p10hiL : PL :=
  [16, 36, 26, 1, 13, 11, 23, 33, 43, 2, 10, 14, 21, 31, 41, 0, 15, 40, 34, 25, 20, 44, 35, 30, 24,
   12, 38, 17, 5, 18, 27, 4, 28, 37, 3, 9, 29, 7, 22, 39, 6, 32, 19, 8, 42]

theorem p10_h_check : p10hL = evalSL [3, 1, 2, 3, 4, 5] ∧ p10hiL = evalSL [5, 4, 3, 1, 2, 3] := by
  decide +kernel

@[expose] def p10hA : Ah := wordSA [3, 1, 2, 3, 4, 5]

@[expose] def alphaL (l : PL) : PL := phiL (comp (comp p10hL l) p10hiL)

theorem p10_K_check :
    p10Kl.Nodup ∧ p10Kl.length = 96 ∧ (∀ w ∈ p10Kw, ∀ k ∈ w, k < 6) ∧
    (∀ l ∈ p10Kl, comp l p10fL = comp p10fL l) ∧
    comp p10hL p10fL ≠ comp p10fL p10hL ∧ p10fL ∈ p10Kl ∧ comp p10hL p10hL ∈ p10Kl ∧
    comp p10hL p10hiL = idL ∧ p10hiL.length = 45 ∧ (∀ x ∈ p10hiL, x < 45) ∧
    (∀ k < 6, comp (p10eSymL.getD k idL) p10fL = comp p10fL (p10eSymL.getD k idL)) := by
  decide +kernel

@[expose] def NormA2 (l : PL) : Prop := ∀ a ∈ Al2, ∃ a' ∈ Al2, comp l a = comp a' l

instance (l : PL) : Decidable (NormA2 l) := by unfold NormA2; infer_instance

theorem p10_norm_check : (∀ l ∈ p10Kl, NormA2 l) ∧ NormA2 p10hL := by decide +kernel

@[expose] def p10Kg : List PL := [p10Kl.getD 1 [], p10Kl.getD 2 [], p10Kl.getD 34 []]

theorem p10_uniq_check : (∀ l ∈ p10Kg, l ∈ p10Kl) ∧ ∀ n ∈ p10Kl,
    (∀ l ∈ p10Kg, comp n l = comp (alphaL (alphaL (alphaL l))) n) → alphaL n = n → n = idL := by
  decide +kernel

end CFSG.Quasithin.H13.F431.U42Aut
