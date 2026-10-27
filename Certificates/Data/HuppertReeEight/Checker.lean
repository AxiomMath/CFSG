module

public import Certificates.Data.HuppertReeEight.Data
public import CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.Sporadic.Schreier.TitsArrays
public import CFSG.Certificates.NativeSchreierCard
public import Mathlib.GroupTheory.Schreier

public section

namespace HuppertReeEight

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def aArr (w : List Int) : Array Nat := wordArr 1755 titsGenArrs w

@[expose] def commE (x y : Array Nat) : Bool := eqA 1755 (compA 1755 x y) (compA 1755 y x)

@[expose] def cubeE (x : Array Nat) : Bool := eqA 1755 (compA 1755 (compA 1755 x x) x) (idA 1755)

@[expose] def oneE (x : Array Nat) : Bool := eqA 1755 x (idA 1755)

@[expose] def memE (L : List (Array Nat)) (x : Array Nat) : Bool := L.any fun c => eqA 1755 x c

@[expose] def powsE (x : Array Nat) : List (Array Nat) := [idA 1755, x, compA 1755 x x]

@[expose] def planeE (u v : Array Nat) : List (Array Nat) :=
  (powsE u).flatMap fun a => (powsE v).map fun b => compA 1755 a b

@[expose] def isPairE (x y : Array Nat) : Bool :=
  !oneE x && cubeE x && cubeE y && commE x y && !(memE (powsE x) y)

@[expose] def invWord (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def zWord : List Int := invWord xWord ++ invWord yWord ++ xWord ++ yWord

@[expose] def powWord (w : List Int) : Nat → List Int
  | 0 => []
  | k + 1 => w ++ powWord w k

@[expose] def sylWords : List (List Int) :=
  (List.range 27).map fun k => powWord xWord (k / 9) ++ powWord yWord (k / 3 % 3) ++ powWord zWord (k % 3)

@[expose] def sylArrs (_ : Unit := ()) : List (Array Nat) := sylWords.map aArr

structure PlaneDatum where
  u : List Int
  v : List Int
  gu : List (List Int)
  gv : List (List Int)
  prog : List (List Int)

@[expose] def planeData : List PlaneDatum :=
  [⟨zWord, xWord, cenZ, cenV.getD 0 [], slp.getD 0 []⟩,
   ⟨zWord, yWord, cenZ, cenV.getD 1 [], slp.getD 1 []⟩,
   ⟨zWord, xWord ++ yWord, cenZ, cenV.getD 2 [], slp.getD 2 []⟩,
   ⟨zWord, xWord ++ yWord ++ yWord, cenZ, cenV.getD 3 [], slp.getD 3 []⟩]

@[expose] def sylowCheck (_ : Unit := ()) : Bool :=
  let E := sylArrs ()
  decide (sylWords.length = 27) && sylWords.all (lettersOK 4) && E.all cubeE &&
    E.all (fun a => E.all fun b => memE E (compA 1755 a b)) &&
    decide (E.Pairwise fun a b => eqA 1755 a b = false)

@[expose] def coverCheck (_ : Unit := ()) : Bool :=
  let E := sylArrs ()
  let planes := planeData.map fun d => planeE (aArr d.u) (aArr d.v)
  let Om := E.filter fun x => !oneE x
  planeData.all (fun d => lettersOK 4 d.u && lettersOK 4 d.v && isPairE (aArr d.u) (aArr d.v)) &&
    Om.all fun x => Om.all fun y =>
      memE (powsE x) y || !commE x y || planes.any fun P => memE P x && memE P y

@[expose] def genCheckAt (d : PlaneDatum) : Bool :=
  let u := aArr d.u
  let v := aArr d.v
  let Cl : List (Array Nat) := (d.gu ++ d.gv).map aArr
  let Cs : Array (Array Nat) := Cl.toArray
  (d.gu ++ d.gv).all (lettersOK 4) && d.gu.all (fun w => commE u (aArr w)) &&
    d.gv.all (fun w => commE v (aArr w)) &&
    Cl.all (fun c => isInvA 1755 c (invCand 1755 c)) && decide (d.prog.length = 4) &&
    (List.range 4).all fun i =>
      lettersOK Cs.size (d.prog.getD i []) &&
        eqA 1755 titsGenArrs[i]! (wordArr 1755 Cs (d.prog.getD i []))

@[expose] def genCheck (_ : Unit := ()) : Bool := planeData.all genCheckAt

end HuppertReeEight
