module

public import CFSG.Sporadic.J4.Group
public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

@[expose] noncomputable def letterElt (l : ℕ) : J := if l = 1 then a else b

@[expose] noncomputable def pathElt : List ℕ → J
  | [] => 1
  | l :: ls => letterElt l * pathElt ls

theorem letterElt_one : letterElt 1 = a := by simp [letterElt]

theorem letterElt_two : letterElt 2 = b := by simp [letterElt]

theorem repPaths_letters : ∀ ℓ < 7, ∀ l ∈ repPaths.getD ℓ [], l = 1 ∨ l = 2 := by
  intro ℓ hℓ
  interval_cases ℓ <;> simp [repPaths]

end CFSG.Sporadic.J4.QT2
