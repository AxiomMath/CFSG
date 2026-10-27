
module

public import CFSG.Sporadic.ThSchreier.CentralizerDataBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

@[expose] def invWord (w : List ℤ) : List ℤ := (w.map fun l => -l).reverse

theorem pairLetters_neg {G : Type*} [Group G] (g h : G) {l : ℤ} (hl : l = 1 ∨ l = 2) :
    pairLetters g h (-l) = (pairLetters g h l)⁻¹ := by
  rcases hl with rfl | rfl <;> simp [pairLetters]

theorem wordG_invWord {G : Type*} [Group G] (g h : G) :
    ∀ w : List ℤ, (∀ l ∈ w, l = 1 ∨ l = 2) →
      wordG (pairLetters g h) (invWord w) = (wordG (pairLetters g h) w)⁻¹
  | [], _ => by simp [invWord, wordG]
  | l :: w, hw => by
    have ih := wordG_invWord g h w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have e : invWord (l :: w) = invWord w ++ [-l] := by simp [invWord]
    rw [e]
    unfold wordG at ih ⊢
    rw [List.map_append, List.prod_append, ih, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, List.map_cons, List.prod_cons,
      pairLetters_neg g h (hw l List.mem_cons_self), mul_inv_rev]

theorem transporterWord_letters : ∀ l ∈ transporterWord, l = 1 ∨ l = 2 := by decide

@[expose] def rowsV : Array V4 := abRows transporterWord

@[expose] def rowsVInv : Array V4 := abRows (invWord transporterWord)

@[expose] def starKey : Key := imageKey (frTable rowsVInv) wKeyRow

end CFSG.Sporadic.ThSchreier
