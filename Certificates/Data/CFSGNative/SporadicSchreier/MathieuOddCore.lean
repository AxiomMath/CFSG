module

public import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace CFSG.Sporadic.Schreier.Native

open CFSG.Sporadic.Th.Native

@[expose] def commT (n : Nat) (x y : Table) : Bool := tblEq n (compT n x y) (compT n y x)

@[expose] def commAll (n : Nat) (gens : List Table) (e : Table) : Bool :=
  gens.all fun g => commT n e g

@[expose] def allTrue (_ : Table) : Bool := true

@[expose] def repsOK (n : Nat) (gens gensInv : Array Table) (X reps : List Table) (cap : Nat) :
    Bool :=
  let cl := reps.map fun r => (r, conjClosure n gens gensInv r cap)
  cl.all (fun c => conjTreeOK n gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2) &&
    keysDistinct n (cl.flatMap fun c => c.2.1.toList) &&
    (cl.map fun c => c.2.1.size).sum == X.length

@[expose] def repSizes (n : Nat) (gens gensInv : Array Table) (reps : List Table) (cap : Nat) :
    List Nat :=
  reps.map fun r => (conjClosure n gens gensInv r cap).1.size

@[expose] def repsTotal (n : Nat) (gens gensInv : Array Table) (reps Y : List Table) (cap : Nat)
    (r : Table → Table → Bool) : Nat :=
  (reps.map fun x => (conjClosure n gens gensInv x cap).1.size * Y.countP (r x)).sum

@[expose] def wordTbls (x y : Table) (mx my : Nat) (w : List Nat) : List Table :=
  w.flatMap fun l =>
    if l = 0 then [x] else if l = 1 then [y] else if l = 2 then List.replicate (mx - 1) x
    else List.replicate (my - 1) y

@[expose] def wordsTest (n mx my : Nat) (ws : List (List Nat × Nat)) (x y : Table) : Bool :=
  ws.all fun p => ordW n (wordTbls x y mx my p.1) p.2

@[expose] def oddWitnessOK (n m : Nat) (K : List Table) : Bool :=
  K.all fun x => tblEq n x (idT n) || !powFixW n [x] m ||
    K.any (fun h => let hi := invT n h; invOK n h hi && !powFixW n [x, h, x, hi] m) ||
    K.any fun h₁ => let i₁ := invT n h₁; invOK n h₁ i₁ &&
      K.any fun h₂ => let i₂ := invT n h₂; invOK n h₂ i₂ &&
        !powFixW n [x, h₁, x, i₁, h₂, x, i₂] m

end CFSG.Sporadic.Schreier.Native
