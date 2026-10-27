module

public import Certificates.Data.GH74.AE117

public section

namespace Certificates.AE7OddGen

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

@[expose] def Lrel (t : Fin 7 → Fin 7) : List (Wr 7) :=
  [⟨0, List.formPerm [t 0, t 1, t 2]⟩, ⟨0, List.formPerm [t 1, t 2, t 3]⟩,
    ⟨0, List.formPerm [t 0, t 1, t 6]⟩, ⟨0, List.formPerm [t 4, t 5, t 6]⟩,
    ⟨indL [t 0, t 1], List.formPerm [t 0, t 1, t 2]⟩]

@[expose] def flagList (α : Finset (Fin 7)) (p q : Fin 7) : List (Fin 7) :=
  α.sort (· ≤ ·) ++ [p, q] ++ (List.finRange 7).filter fun i => decide (i ∉ α ∧ i ≠ p ∧ i ≠ q)

@[expose] def flagFun (α : Finset (Fin 7)) (p q : Fin 7) : Fin 7 → Fin 7 :=
  fun i => (flagList α p q).getD i.val i

@[expose] def W₁ : List (List ℕ) :=
  [[0, 9], [1, 8], [2, 1, 8, 3], [6, 5, 0, 9, 4, 7], [7, 5, 0, 9, 4, 6], [5, 0, 9, 4], [0, 8, 0],
    [0, 2, 9, 1, 2], [1, 6, 5, 9, 5, 7], [1, 7, 5, 9, 5, 6], [1, 5, 9, 5], [1, 3, 8, 0, 3],
    [0, 6, 4, 8, 4, 7], [0, 7, 4, 8, 4, 6], [0, 4, 8, 4], [0, 2, 6, 5, 9, 5, 2, 7],
    [0, 2, 7, 5, 9, 5, 2, 6], [0, 2, 5, 9, 5, 2], [6, 4, 8, 4, 6, 5, 9, 5, 6],
    [4, 1, 6, 5, 9, 5, 7, 5], [4, 1, 7, 5, 9, 5, 6, 5]]

@[expose] def W₂ : List (List ℕ) :=
  [[6], [7], [3, 5, 6, 4, 2], [3, 5, 6, 4, 2, 7], [3, 5, 7, 4, 2], [3, 5, 7, 4, 2, 6],
    [3, 6, 5, 7, 4, 2], [3, 7, 5, 6, 4, 2], [1, 6, 4, 2, 7], [1, 7, 4, 2, 6], [1, 4, 2],
    [3, 6, 5, 0, 7], [0, 5, 6, 4, 1], [0, 5, 6, 4, 1, 7], [3, 7, 5, 0, 6], [0, 5, 7, 4, 1],
    [0, 5, 7, 4, 1, 6], [3, 5, 0], [0, 6, 5, 7, 4, 1], [0, 7, 5, 6, 4, 1], [2], [6, 5, 0, 7],
    [7, 5, 0, 6], [5, 0], [3], [6, 5, 0, 3, 7], [7, 5, 0, 3, 6], [5, 0, 3], [1, 6, 4, 7],
    [2, 1, 6, 4, 7], [5, 6, 4], [5, 6, 4, 7], [1, 7, 4, 6], [2, 1, 7, 4, 6], [5, 7, 4],
    [5, 7, 4, 6], [1, 4], [2, 1, 4], [6, 5, 7, 4], [7, 5, 6, 4], [0], [0, 3], [6, 4, 7], [7, 4, 6],
    [4], [1], [1, 2], [6, 4, 1, 7], [7, 4, 1, 6], [4, 1], [2, 1], [3, 0], [3, 6, 4, 2, 7],
    [3, 7, 4, 2, 6], [3, 4, 2], [6, 5, 7], [0, 6, 5, 7], [0, 3, 6, 5, 7], [4, 6, 5], [4, 6, 5, 7],
    [7, 5, 6], [0, 7, 5, 6], [0, 3, 7, 5, 6], [4, 7, 5], [4, 7, 5, 6], [5], [0, 5], [0, 3, 5],
    [6, 4, 7, 5], [7, 4, 6, 5]]

@[expose] def eqWr (x y : Wr 7) : Bool :=
  (List.finRange 7).all fun i => decide (x.vec i = y.vec i) && decide (x.perm i = y.perm i)

@[expose] def keyV (x : Wr 7) : List (ZMod 2) := (List.finRange 7).map x.vec

@[expose] def keyP (σ : Equiv.Perm (Fin 7)) : List (Fin 7) := (List.finRange 7).map σ

@[expose] def commOK (L : List (Wr 7)) (g z : Wr 7) : Bool :=
  L.all fun b => eqWr (b * g) (g * b) || eqWr (b * z) (z * b)

@[expose] def aeOK (L : List (Wr 7)) : Bool :=
  L.all fun b => decide (wsum b = 0) && decide (Equiv.Perm.sign b.perm = 1) && eqWr (b ^ 15) 1

@[expose] def pairsOK (L : List (Wr 7)) : Bool :=
  let ks := W₁.map fun w => (keyP (evalG L w).perm, keyV (evalG L w))
  (List.finRange 7).all fun j => (List.finRange 7).all fun k =>
    decide (j = k) || ks.contains (keyP 1, keyV (ofVec (indL [j, k])))

@[expose] def cyclesOK (L : List (Wr 7)) : Bool :=
  let ks := W₂.map fun w => keyP (evalG L w).perm
  (List.finRange 7).all fun a => (List.finRange 7).all fun b => (List.finRange 7).all fun c =>
    decide (a = b) || decide (b = c) || decide (a = c) ||
      ks.contains (keyP (Equiv.swap a b * Equiv.swap b c))

@[expose] def flagOK (α : Finset (Fin 7)) (p q : Fin 7) : Bool :=
  let L := Lrel (flagFun α p q)
  commOK L (ofVec (indL [p, q])) (ofVec (indF α)) && aeOK L && pairsOK L && cyclesOK L

abbrev oddGenProp : Prop :=
  ∀ α ∈ (Finset.univ : Finset (Fin 7)).powersetCard 4, ∀ p q : Fin 7, p ∉ α → q ∉ α → p ≠ q →
    flagOK α p q = true

@[expose] def oddGenCheck (_ : Unit) : Bool := decide oddGenProp

end Certificates.AE7OddGen
