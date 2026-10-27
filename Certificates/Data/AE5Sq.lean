module

public import Certificates.Data.GH74.AE117

public section

namespace Certificates.AE5Sq

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

@[expose] def cyc5 (cs : List (List Nat)) : Equiv.Perm (Fin 5) :=
  (cs.map fun c => (c.map fun i => (Fin.ofNat 5 i)).formPerm).prod

@[expose] def vec5 (s : List Nat) : Fin 5 → ZMod 2 := fun i => if i.val ∈ s then 1 else 0

@[expose] def a0 (_ : Unit := ()) : Wr 5 := ⟨vec5 [], cyc5 [[0, 1, 2, 3, 4]]⟩

@[expose] def b0 (_ : Unit := ()) : Wr 5 := ⟨vec5 [3, 4], cyc5 [[1, 2], [3, 4]]⟩

@[expose] def alphas : List (Finset (Fin 5)) := [{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}]

@[expose] def words8 : List (List ℕ) := [[], [0, 0], [0], [0, 0, 0], [2], [2, 2, 2], [0, 2], [0, 2, 0, 2, 0, 2]]

@[expose] def a5Fin (_ : Unit := ()) : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.filter fun σ => Equiv.Perm.sign σ = 1

@[expose] def evenFin5 (_ : Unit := ()) : Finset (Fin 5 → ZMod 2) :=
  Finset.univ.filter fun v => ∑ i, v i = 0

@[expose] def finAll {α : Type} (s : Finset α) (f : α → Bool) : Bool := decide (∀ x ∈ s, f x = true)

@[expose] def ord4Pi (x : Wr 5) : Bool := !inPi (x * x) && inPi (x * x * (x * x))

@[expose] def q8Pair (x y : Wr 5) : Bool :=
  ord4Pi x && eqPi (y * y) (x * x) && eqPi (x * y * (x * y)) (x * x) && !eqPi y x && !eqPi y (x * x * x)

@[expose] def inMem (α : Finset (Fin 5)) (b : Bool) (x : Wr 5) : Bool := (memAtL α b).any fun m => eqPi m x

@[expose] def genOK (_ : Unit := ()) : Bool :=
  alphas.all fun α => [true, false].all fun b =>
    let L := memAtL α b
    let i := L.getD 2 1
    let j := L.getD 4 1
    decide (i ∈ L) && decide (j ∈ L) && q8Pair i j &&
      L.all fun m => words8.any fun w => eqPi (evalG [i, j] w) m

@[expose] def pairsOK (A5 : Finset (Equiv.Perm (Fin 5))) (Ev : Finset (Fin 5 → ZMod 2)) : Bool :=
  finAll A5 fun τx => finAll Ev fun vx =>
    !(ord4Pi ⟨vx, τx⟩) || finAll A5 fun τy => finAll Ev fun vy =>
      !(q8Pair ⟨vx, τx⟩ ⟨vy, τy⟩) ||
        alphas.any fun α => [true, false].any fun b => inMem α b ⟨vx, τx⟩ && inMem α b ⟨vy, τy⟩

@[expose] def sqOK (P : Finset (Equiv.Perm (Fin 5))) (V : Finset (Fin 5 → ZMod 2)) : Bool :=
  finAll P fun τ => finAll V fun v =>
    let c : Wr 5 := ⟨v, τ⟩
    let c2 := c * c
    let c4 := c2 * c2
    !(eqPi (c4 * a0 ()) (a0 () * c4) && eqPi (c4 * b0 ()) (b0 () * c4)) ||
      alphas.any fun α => [true, false].any fun b =>
        (memAtL α b).any fun y => ord4Pi y && eqPi (c2 * y) (y * c2)

@[expose] def check (_ : Unit := ()) : Bool :=
  decide ((a0 ()).vec ∈ evenFin5 ()) && decide ((a0 ()).perm ∈ a5Fin ()) &&
    decide ((b0 ()).vec ∈ evenFin5 ()) && decide ((b0 ()).perm ∈ a5Fin ()) &&
    genOK () && pairsOK (a5Fin ()) (evenFin5 ()) && sqOK Finset.univ Finset.univ

end Certificates.AE5Sq
