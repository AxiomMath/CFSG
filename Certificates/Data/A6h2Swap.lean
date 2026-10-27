module

public import Certificates.Data.AE6ModelCore

public section

namespace Certificates.A6h2Swap

open Certificates.AE6Model

@[expose] def swapMap : List (List ℕ) :=
  [[0, 1, 2, 3, 6, 7, 4, 5], [4, 5, 2, 3, 0, 1, 6, 7], [6, 7, 2, 3, 4, 5, 0, 1]]

@[expose] def swapConj : List (List ℕ) := [[], [6], [4]]

@[expose] def k0Elts (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let K := k0Gens ()
  let a := K.getD 0 1
  let b := K.getD 1 1
  [1, a, a⁻¹, b, b⁻¹, a * b, (a * b)⁻¹, a * a]

@[expose] def swapCheck (_ : Unit := ()) : Bool :=
  let G := curtisPerms ()
  let E := k0Elts ()
  (List.range 3).all fun k =>
    let c := aeWord G (swapConj.getD k [])
    kWords.all fun w =>
      let x := aeWord G (w.map fun i => (swapMap.getD k []).getD i 0)
      E.contains (c⁻¹ * x * c)

end Certificates.A6h2Swap
