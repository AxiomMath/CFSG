module

public import CFSG.Quasithin.Recognition.M12AscCoxInputs

public section

namespace CFSG.Quasithin

@[expose] def swapGen (i : Fin 5) : Equiv.Perm (Fin 6) := Equiv.swap i.castSucc i.succ

@[expose] def evalWord {M : Type*} [Monoid M] (f : Fin 5 → M) (w : List (Fin 5)) : M :=
  (w.map f).prod

theorem hom_apply_word {M : Type*} [Group M] (h : Equiv.Perm (Fin 6) →* M)
    {σ : Equiv.Perm (Fin 6)} {w : List (Fin 5)} (hw : evalWord swapGen w = σ) :
    h σ = evalWord (fun i => h (swapGen i)) w := by
  rw [← hw]
  unfold evalWord
  rw [map_list_prod, List.map_map]
  rfl

end CFSG.Quasithin
