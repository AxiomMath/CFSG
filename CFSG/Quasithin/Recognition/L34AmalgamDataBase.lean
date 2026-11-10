
module

public import CFSG.Quasithin.Recognition.M22WittData
public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public import CFSG.Quasithin.Recognition.L34AmalgamDataInputs

@[expose] public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.Sporadic.Mathieu

theorem evalW_eq_lift {X : Type*} [Group X] (f : Fin 5 → X) (w : List (Fin 5 × Bool)) :
    evalW f w = FreeGroup.lift f (FreeGroup.mk w) := by
  rw [evalW, FreeGroup.lift_mk]

theorem evalW_append {X : Type*} [Group X] (f : Fin 5 → X) (v w : List (Fin 5 × Bool)) :
    evalW f (v ++ w) = evalW f v * evalW f w := by
  rw [evalW, List.map_append, List.prod_append]
  rfl

theorem evalW_map {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) (f : Fin 5 → X)
    (g : Fin 5 → Y) (w : List (Fin 5 × Bool)) (h : ∀ x ∈ w, g x.1 = φ (f x.1)) :
    evalW g w = φ (evalW f w) := by
  rw [evalW, evalW, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun x hx => ?_
  rcases x with ⟨i, b⟩
  cases b <;> simp [h _ hx]

def relsOf (i : Fin 12) (k : ℕ) : List (List (Fin 5 × Bool)) := amalRels ++ [extra i k]

def rep (i : Fin 12) : M22 := evalW gen (word (repStr i))

theorem letters_facts : (∀ s ∈ rels1, ∀ x ∈ word s, x.1 ≠ 4) ∧ (∀ s ∈ rels2, ∀ x ∈ word s, x.1 ≠ 3)
    ∧ ∀ i : Fin 12, ∀ x ∈ word (repStr i), x.1 ≠ 3 := by
  decide

theorem word_s : word "s" = [(3, true)] := by decide

theorem extra_succ (i : Fin 12) (k : ℕ) :
    extra i (k + 1) = word "s" ++ word (repStr i) ++ extra i k := by
  simp only [extra, word, List.replicate_succ, String.join_cons, String.toList_append,
    List.map_append, List.append_assoc]

theorem evalW_extra {X : Type*} [Group X] (f : Fin 5 → X) (i : Fin 12) (k : ℕ) :
    evalW f (extra i k) = (f 3 * evalW f (word (repStr i))) ^ k := by
  induction k with
  | zero => simp [extra, word, evalW]
  | succ k ih =>
    have h3 : evalW f [(3, true)] = f 3 := by simp [evalW]
    rw [extra_succ, evalW_append, evalW_append, ih, word_s, h3, pow_succ']

theorem gen_three : gen 3 = bT1 := rfl

theorem gen_four : gen 4 = bT2 := rfl

end CFSG.Quasithin.L34Amalgam
