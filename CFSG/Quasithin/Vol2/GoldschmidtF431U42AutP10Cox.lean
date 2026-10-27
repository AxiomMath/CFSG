module

public import Certificates.Data.H13.U42AutP10Rel
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cls

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 f45)

@[expose] def p10sW : List (List ℕ) :=
  [[1, 0, 1, 1, 0, 2, 3, 2, 0, 2, 2],
   [1, 1, 0, 2, 2, 0, 1, 0, 1, 3, 2],
   [0, 1, 1, 3, 2, 0, 3, 1, 1, 3, 2],
   [1, 0, 2, 2, 0, 1, 0, 1, 3],
   [1, 0, 1, 0, 1, 3, 1, 0, 1, 1],
   [0, 1, 0, 1, 3, 1, 0, 2, 2]]

@[expose] def p10sL : List PL :=
  [[35, 15, 25, 14, 12, 13, 6, 7, 8, 9, 10, 11, 4, 5, 3, 1, 42, 17, 31, 32, 37, 21, 22, 27, 41, 2,
    39, 23, 28, 29, 43, 18, 19, 33, 38, 0, 36, 20, 34, 26, 40, 24, 16, 30, 44],
   [0, 1, 2, 12, 14, 13, 9, 11, 10, 6, 8, 7, 3, 5, 4, 15, 16, 22, 19, 18, 24, 21, 17, 23, 20, 25,
    30, 27, 33, 29, 26, 32, 31, 28, 34, 35, 44, 41, 38, 43, 40, 37, 42, 39, 36],
   [0, 21, 23, 3, 28, 37, 6, 32, 39, 9, 43, 31, 12, 41, 33, 15, 16, 17, 18, 19, 24, 1, 22, 2, 20,
    34, 26, 38, 4, 42, 30, 11, 7, 14, 25, 40, 36, 5, 27, 8, 35, 13, 29, 10, 44],
   [0, 1, 2, 13, 12, 14, 10, 9, 11, 7, 6, 8, 4, 3, 5, 15, 20, 17, 23, 19, 16, 22, 21, 18, 24, 25,
    34, 31, 28, 33, 30, 27, 32, 29, 26, 35, 36, 42, 39, 38, 44, 41, 37, 43, 40],
   [16, 1, 23, 30, 39, 5, 44, 7, 28, 36, 33, 11, 26, 13, 43, 15, 0, 22, 18, 19, 20, 21, 17, 2, 24,
    27, 12, 25, 8, 40, 3, 31, 32, 10, 38, 42, 9, 37, 34, 4, 29, 41, 35, 14, 6],
   [15, 35, 25, 3, 4, 5, 9, 10, 11, 6, 7, 8, 12, 13, 14, 0, 16, 36, 26, 30, 20, 40, 44, 34, 24, 2,
    18, 38, 28, 29, 19, 39, 43, 33, 23, 1, 17, 37, 27, 31, 21, 41, 42, 32, 22]]

theorem p10sL_eq : p10sL = p10sW.map evalAL := by decide +kernel

@[expose] def p10sA (k : ℕ) : Ah := aW (p10sW.getD k [])

@[expose] def evalSL (w : List ℕ) : PL := w.foldr (fun k acc => comp (p10sL.getD k idL) acc) idL

@[expose] def wordSA (w : List ℕ) : Ah := (w.map p10sA).prod

theorem repL_p10sA (k : ℕ) : RepL (p10sL.getD k idL) ((p10sA k : Ah) : P45) := by
  have h : p10sL.getD k idL = evalAL (p10sW.getD k []) := by
    rw [p10sL_eq]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases p10sW[k]? <;> rfl
  rw [h]
  exact repL_aW _

theorem repL_wordSA (w : List ℕ) : RepL (evalSL w) ((wordSA w : Ah) : P45) := by
  induction w with
  | nil => exact repL_one 45
  | cons k w ih =>
    have h1 := repL_mul (repL_p10sA k) ih
    exact h1

theorem wordSA_eq_one {w : List ℕ} (h : evalSL w = idL) : wordSA w = 1 :=
  Subtype.ext (eq_of_repL (repL_wordSA w) (h ▸ repL_one 45))

theorem wordSA_eq {w : List ℕ} {a : Ah} {l : PL} (h : evalSL w = l) (ha : RepL l (a : P45)) :
    wordSA w = a :=
  Subtype.ext (eq_of_repL (repL_wordSA w) (h ▸ ha))

@[expose] def relN (r : List (Fin 7 × Bool)) : List ℕ := r.map fun l => l.1.val

theorem cox_check : ∀ r ∈ p10Cox, evalSL (relN r) = idL := by decide +kernel

@[expose] def p10tA : Ah := wordSA [3, 1, 2, 3, 4, 3, 1, 2, 3]

theorem wordSA_cox : ∀ r ∈ p10Cox, wordSA (relN r) = 1 := fun r hr => wordSA_eq_one (cox_check r hr)

@[expose] def p10xW : List ℕ := [1, 2, 3, 1, 2, 3, 5, 4, 3, 1, 2, 3, 4, 5]

@[expose] def p10yW : List ℕ := [1, 3, 1, 2, 3, 4, 3, 1, 2, 0, 3, 4, 5, 4, 3, 1]

@[expose] def p10fW : List ℕ := [1, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 3, 4, 5]

theorem p10_gen_check : evalSL p10xW = xL ∧ evalSL p10yW = yL ∧ evalSL p10fW = f45L := by
  decide +kernel

theorem wordSA_mem_closure (w : List ℕ) (hw : ∀ k ∈ w, k < 6) :
    wordSA w ∈ Subgroup.closure (Set.range fun i : Fin 6 => p10sA i) := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
  exact Subgroup.subset_closure ⟨⟨k, hw k hk⟩, rfl⟩

theorem closure_p10sA : Subgroup.closure (Set.range fun i : Fin 6 => p10sA i) = ⊤ := by
  set C := Subgroup.closure (Set.range fun i : Fin 6 => p10sA i) with hC
  have hx : (⟨x45, x45_mem_A⟩ : Ah) ∈ C := by
    rw [← wordSA_eq (a := (⟨x45, x45_mem_A⟩ : Ah)) p10_gen_check.1 repL_x]
    exact wordSA_mem_closure _ (by decide)
  have hy : (⟨y45, y45_mem_A⟩ : Ah) ∈ C := by
    rw [← wordSA_eq (a := (⟨y45, y45_mem_A⟩ : Ah)) p10_gen_check.2.1 repL_y]
    exact wordSA_mem_closure _ (by decide)
  have hf : (⟨f45, f45_mem_A⟩ : Ah) ∈ C := by
    rw [← wordSA_eq (a := (⟨f45, f45_mem_A⟩ : Ah)) p10_gen_check.2.2 repL_f45]
    exact wordSA_mem_closure _ (by decide)
  have key : ∀ g ∈ Subgroup.closure ({x45, y45, f45} : Set P45),
      ∃ h : g ∈ QA45.originalSubgroup, (⟨g, h⟩ : Ah) ∈ C := by
    intro g hg
    refine Subgroup.closure_induction
      (p := fun g _ => ∃ h : g ∈ QA45.originalSubgroup, (⟨g, h⟩ : Ah) ∈ C) ?_ ?_ ?_ ?_ hg
    · rintro g (rfl | rfl | rfl)
      · exact ⟨x45_mem_A, hx⟩
      · exact ⟨y45_mem_A, hy⟩
      · exact ⟨f45_mem_A, hf⟩
    · exact ⟨QA45.originalSubgroup.one_mem, C.one_mem⟩
    · rintro g h _ _ ⟨hg, hgC⟩ ⟨hh, hhC⟩
      exact ⟨QA45.originalSubgroup.mul_mem hg hh, C.mul_mem hgC hhC⟩
    · rintro g _ ⟨hg, hgC⟩
      exact ⟨QA45.originalSubgroup.inv_mem hg, C.inv_mem hgC⟩
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨g, hg⟩ := a
  obtain ⟨h, hC'⟩ := key g (QA45_closure_eq ▸ hg)
  exact hC'

end CFSG.Quasithin.H13.F431.U42Aut
