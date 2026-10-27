module

public import Certificates.Data.Foote82OmegaSix

public section

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def rMat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def rAMat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 1, 0, 1, 1, 1; 1, 1, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1;
    1, 0, 1, 1, 1, 0; 1, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0]

@[expose] def rBMat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 1, 0, 1, 0, 1; 1, 1, 1, 1, 0, 0; 1, 0, 0, 1, 0, 0;
    0, 1, 1, 1, 0, 1; 0, 1, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def a6Rels : List (List ℕ) :=
  [[1, 1, 1, 1], [0, 0], [0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]]

@[expose] def genO (_ : Unit := ()) : Array (Array ℕ) := #[marr aMat, marr bMat, marr rMat]

@[expose] def genOInv (_ : Unit := ()) : Array (Array ℕ) :=
  #[marr aMat, marr (bMat * (bMat * (bMat * bMat))), marr rMat]

@[expose] def oEnum (_ : Unit := ()) : Enum := bfsEnum (genO ()) 51840

@[expose] def conjStep (gs gsInv : Array (Array ℕ)) (E : Enum) (q : ℕ) : Enum := Id.run do
  let x := E.elems[q]!
  let mut E := E
  for j in [0:gs.size] do
    let y := compA (compA gs[j]! x) gsInv[j]!
    if !E.index.contains y then
      let n := E.elems.size
      E := ⟨E.elems.push y, E.parent.push q, E.gen.push j, E.index.insert y n⟩
  return E

@[expose] def conjEnum (gs gsInv : Array (Array ℕ)) (x : Array ℕ) (fuel : ℕ) : Enum := Id.run do
  let mut E : Enum := ⟨#[x], #[0], #[0], ({} : Std.HashMap (Array ℕ) ℕ).insert x 0⟩
  for q in [0:fuel] do
    if q < E.elems.size then
      E := conjStep gs gsInv E q
  return E

@[expose] def conjTreeOK (E : Enum) (gs gsInv : Array (Array ℕ)) (x : Array ℕ) : Bool :=
  decide (E.elems[0]? = some x) &&
    allLt E.elems.size fun i => decide (i = 0) ||
      (decide (E.parent[i]! < i) && decide (E.gen[i]! < gs.size) &&
        decide (E.elems[i]! =
          compA (compA gs[E.gen[i]!]! E.elems[E.parent[i]!]!) gsInv[E.gen[i]!]!))

@[expose] def classA (_ : Unit := ()) : Enum := conjEnum (genO ()) (genOInv ()) (marr rAMat) 100

@[expose] def classB (_ : Unit := ()) : Enum := conjEnum (genO ()) (genOInv ()) (marr rBMat) 400

@[expose] def rank1 (t : Array ℕ) : Bool :=
  (List.range 64).any fun c => c != 0 && ((List.range 64).any fun k => (t[k]! ^^^ k) == c) &&
    (List.range 64).all fun k => (t[k]! ^^^ k) == 0 || (t[k]! ^^^ k) == c

@[expose] def reflCheck (_ : Unit := ()) : Bool :=
  isomB rMat && decide (rMat * rMat = 1) && decide (rAMat * rAMat = 1) &&
    decide (rBMat * rBMat = 1)

@[expose] def oEnumCheck (_ : Unit := ()) : Bool :=
  let gs := genO ()
  let E := oEnum ()
  enumOK E gs && E.elems.size == 51840

@[expose] def repCheck (_ : Unit := ()) : Bool :=
  let E := omegaEnum ()
  ((E.lookup (marr rAMat)).isSome) && ((E.lookup (marr rBMat)).isSome)

@[expose] def classCheck (_ : Unit := ()) : Bool :=
  let gs := genO ()
  let gsInv := genOInv ()
  let one := idA ()
  let EA := classA ()
  let EB := classB ()
  let E := omegaEnum ()
  conjTreeOK EA gs gsInv (marr rAMat) && conjTreeOK EB gs gsInv (marr rBMat) &&
    E.elems.all fun x => !(compA x x == one) || x == one || (EA.lookup x).isSome ||
      (EB.lookup x).isSome

@[expose] def centCheck (_ : Unit := ()) : Bool :=
  let one := idA ()
  let E := omegaEnum ()
  let EO := oEnum ()
  [marr rAMat, marr rBMat].all fun x =>
    let C := EO.elems.filter fun t => compA t x == compA x t && !(t == one)
    E.elems.all fun y => !(a6Rels.all fun w => wordA #[x, y] w == one) ||
      C.all fun t => !(compA t y == compA y t) || rank1 t

end CFSG.CGT.Foote82.OmegaSix
