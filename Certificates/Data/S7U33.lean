module

public import Certificates.Data.S5RowsU33
public import Certificates.Data.S7Q8

public section

namespace Certificates.S7U33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups Certificates.S5Rows
  Certificates.S5RowsU33 Certificates.S7Q8

@[expose] def gensA : List (Equiv.Perm (Fin 28)) :=
  [U33.pa, U33.pb, U33.sg0, U33.pa⁻¹, U33.pb⁻¹, U33.sg0⁻¹]

@[expose] def wA (w : List ℕ) : Equiv.Perm (Fin 28) :=
  tab (w.map fun k => gensA.getD k 1).prod

@[expose] def i1 : Equiv.Perm (Fin 28) := wA [1, 3, 2, 1, 2, 0]

@[expose] def j1 : Equiv.Perm (Fin 28) := wA [2, 3, 2, 1]

@[expose] def i2 : Equiv.Perm (Fin 28) := wA [1, 2, 2, 3, 5, 4]

@[expose] def j2 : Equiv.Perm (Fin 28) := wA [3, 4, 5, 0, 1, 0]

@[expose] def sylowA (_ : Unit := ()) : List (Equiv.Perm (Fin 28)) := elemsT QSA

@[expose] def elemsA (_ : Unit := ()) : List (Equiv.Perm (Fin 28)) := elemsT U33.QA

@[expose] def czA (_ : Unit := ()) : List (Equiv.Perm (Fin 28)) :=
  let z := i1 * i1
  (elemsA ()).filter fun x => decide (x * z = z * x)

@[expose] def factPa (_ : Unit := ()) : List (Equiv.Perm (Fin 28)) :=
  let e := U33.sg0
  let c0 := wA [2, 2]
  let c1 := wA [0, 1, 3]
  let c2 := wA [1, 2, 0, 1, 0]
  [c1, e, c1, e⁻¹, c2, c0, c2, e⁻¹, c2]

@[expose] def factPb (_ : Unit := ()) : List (Equiv.Perm (Fin 28)) :=
  let e := U33.sg0
  let c1 := wA [0, 1, 3]
  [e⁻¹, c1, c1, e⁻¹, c1, e, c1, e]

@[expose] def u33S7Basic (_ : Unit := ()) : Bool :=
  q8RelB i1 j1 && q8RelB i2 j2 && decide (i2 * i2 = i1 * i1) && inQP i1 && inQP j1 &&
    !(inQP i2 && inQP j2)

@[expose] def u33S7Class1 (_ : Unit := ()) : Bool :=
  classCheck i1 j1 (sylowA ()) (elemsA ())

@[expose] def u33S7Class2 (_ : Unit := ()) : Bool :=
  classCheck i2 j2 (sylowA ()) (elemsA ())

@[expose] def u33S7Norm (_ : Unit := ()) : Bool :=
  let c := czA ()
  let s := sylowA ()
  normAllB i1 j1 c && normAllB i2 j2 c && normAllB i1 j1 s && normAllB i2 j2 s

@[expose] def u33S7Q8 (_ : Unit := ()) : Bool :=
  q8InCheck (sylowA ()) i1 j1 i2 j2 && q8InCheck (czA ()) i1 j1 i2 j2

@[expose] def u33S7Edge (_ : Unit := ()) : Bool :=
  edgeB i1 j1 i2 j2 U33.sg0 && factB i1 j1 i2 j2 [U33.sg0] U33.pa (factPa ()) &&
    factB i1 j1 i2 j2 [U33.sg0] U33.pb (factPb ()) &&
    factB i1 j1 i2 j2 [U33.sg0] U33.sg0 [U33.sg0]

end Certificates.S7U33
