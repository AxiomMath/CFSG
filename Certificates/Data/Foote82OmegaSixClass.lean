module

public import Certificates.Data.Foote82OmegaSixCent
public import Mathlib.Data.Nat.Count

public section

namespace CFSG.CGT.Foote82.CaseIIClassAux

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.CGT.Foote82.OmegaSix

@[expose] def genA6Inv (_ : Unit := ()) : Array (Array ℕ) :=
  #[marr aMat, marr (bMat * (bMat * (bMat * bMat)))]

@[expose] def omClassR (_ : Unit := ()) : Enum :=
  conjEnum (genA6 ()) (genA6Inv ()) (marr rMat) 100

@[expose] def omClassA (_ : Unit := ()) : Enum :=
  conjEnum (genA6 ()) (genA6Inv ()) (marr rAMat) 100

@[expose] def omClassB (_ : Unit := ()) : Enum :=
  conjEnum (genA6 ()) (genA6Inv ()) (marr rBMat) 400

@[expose] def commB (t u : Array ℕ) : Bool := compA t u == compA u t

@[expose] def centCount (x : Array ℕ) : ℕ :=
  let E := omegaEnum ()
  Nat.count (fun i => commB E.elems[i]! x = true) E.elems.size

@[expose] def omClassCheck (_ : Unit := ()) : Bool :=
  let gs := genA6 ()
  let gsInv := genA6Inv ()
  let one := idA ()
  let EA := omClassA ()
  let EB := omClassB ()
  let E := omegaEnum ()
  conjTreeOK EA gs gsInv (marr rAMat) && conjTreeOK EB gs gsInv (marr rBMat) &&
    E.elems.all fun x => !(compA x x == one) || x == one || (EA.lookup x).isSome ||
      (EB.lookup x).isSome

@[expose] def centCountCheck (_ : Unit := ()) : Bool :=
  centCount (marr rMat) == 720 && centCount (marr rAMat) == 576 && centCount (marr rBMat) == 96

@[expose] def subOneCode (t : Array ℕ) (k : ℕ) : ℕ := t[k]! ^^^ k

@[expose] def twoNZ (t : Array ℕ) : Bool :=
  (List.range 64).any fun i => subOneCode t i != 0 &&
    (List.range 64).any fun j => subOneCode t j != 0 && subOneCode t j != subOneCode t i

@[expose] def reflOrbitCheck (_ : Unit := ()) : Bool :=
  let ER := omClassR ()
  let one := idA ()
  conjTreeOK ER (genA6 ()) (genA6Inv ()) (marr rMat) &&
    (oEnum ()).elems.all fun t => (ER.lookup t).isSome || t == one || twoNZ t

@[expose] def a6cMat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def a6d1Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def a6d2Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 1, 0, 0, 1; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def commArr (x y : Array ℕ) : Array ℕ := compA (compA (compA x y) x) y

@[expose] def a6Gens (_ : Unit := ()) : Array (Array ℕ) :=
  #[commArr (marr a6cMat) (marr a6d1Mat), commArr (marr a6cMat) (marr a6d2Mat)]

@[expose] def a6Enum (_ : Unit := ()) : Enum := bfsEnum (a6Gens ()) 360

@[expose] def isCentInv (E : Enum) (y x : Array ℕ) : Bool :=
  (E.lookup x).isSome && commB x y && compA x x == idA ()

@[expose] def a6Check (_ : Unit := ()) : Bool :=
  let E := omegaEnum ()
  let gs := a6Gens ()
  let ED := a6Enum ()
  let EB := omClassB ()
  let one := idA ()
  isCentInv E (marr rMat) (marr a6cMat) && isCentInv E (marr rMat) (marr a6d1Mat) &&
    isCentInv E (marr rMat) (marr a6d2Mat) && enumOK ED gs && ED.elems.size == 360 &&
    ED.elems.all fun x => !(compA x x == one) || x == one || (EB.lookup x).isSome

@[expose] def a6CentCheck (_ : Unit := ()) : Bool :=
  let gs := a6Gens ()
  let w₁ := gs[0]!
  let w₂ := gs[1]!
  let one := idA ()
  let r := marr rMat
  (oEnum ()).elems.all fun t => !(commB t w₁ && commB t w₂) || t == one || t == r

@[expose] def e1Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1]

@[expose] def e2Mat : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ofBits !![1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def powA (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA ()
  | m + 1 => compA (powA t m) t

@[expose] def powInvol (one y z : Array ℕ) : Bool :=
  (List.range 12).any fun m =>
    let u := powA z (m + 1)
    compA u u == one && !(u == one) && !(u == y)

@[expose] def stepA (e z : Array ℕ) : Array ℕ := compA (compA (compA e z) e) (powA z 11)

@[expose] def good1 (one y : Array ℕ) (es : List (Array ℕ)) (z : Array ℕ) : Bool :=
  powInvol one y z || es.any fun e => powInvol one y (stepA e z)

@[expose] def good2 (one y : Array ℕ) (es : List (Array ℕ)) (z : Array ℕ) : Bool :=
  good1 one y es z || es.any fun e => good1 one y es (stepA e z)

@[expose] def closureCheck (_ : Unit := ()) : Bool :=
  let E := omegaEnum ()
  let y := marr rAMat
  let one := idA ()
  let es := [marr e1Mat, marr e2Mat]
  es.all (isCentInv E y) &&
    E.elems.all fun z => !(commB z y) || z == one || z == y || good2 one y es z

end CFSG.CGT.Foote82.CaseIIClassAux
