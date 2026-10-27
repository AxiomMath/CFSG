module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr

public section

namespace CFSG

namespace FiveTransitive.DisjointFinEmbeddingAppend

theorem exists_append
    {X : Type*} {m n : ℕ} (e : Fin m ↪ X) (f : Fin n ↪ X)
    (hdis : ∀ j : Fin n, f j ∉ Set.range e) :
    ∃ E : Fin (m + n) ↪ X,
      (∀ i : Fin m, E (i.castAdd n) = e i) ∧
      ∀ j : Fin n, E (j.natAdd m) = f j := by
  let F : Fin (m + n) → X := fun i =>
    if h : i.val < m then e ⟨i.val,h⟩ else f ⟨i.val - m,by omega⟩
  have hinj : Function.Injective F := by
    intro i j he
    by_cases hi : i.val < m <;> by_cases hj : j.val < m
    · simp only [F,dif_pos hi,dif_pos hj] at he
      exact Fin.ext (congrArg (fun t : Fin m => t.val) (e.injective he))
    · simp only [F,dif_pos hi,dif_neg hj] at he
      exact (hdis ⟨j.val - m,by omega⟩ ⟨⟨i.val,hi⟩,he⟩).elim
    · simp only [F,dif_neg hi,dif_pos hj] at he
      exact (hdis ⟨i.val - m,by omega⟩ ⟨⟨j.val,hj⟩,he.symm⟩).elim
    · simp only [F,dif_neg hi,dif_neg hj] at he
      have hh := congrArg Fin.val (f.injective he)
      apply Fin.ext
      dsimp only at hh
      omega
  refine ⟨⟨F,hinj⟩,?_,?_⟩
  · intro i
    change F (i.castAdd n) = e i
    simp only [F,Fin.val_castAdd,dif_pos i.isLt]
  · intro j
    change F (j.natAdd m) = f j
    simp only [F,Fin.val_natAdd]
    rw [dif_neg (by omega)]
    congr 1
    apply Fin.ext
    simp

end FiveTransitive.DisjointFinEmbeddingAppend

end CFSG
