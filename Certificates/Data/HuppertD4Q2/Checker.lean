module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterRep
public import Certificates.Data.HuppertD4Q2.Data
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace HuppertD4Q2

open CFSG.AGLEmbedding.D4Two CFSG.AGLEmbedding.ChevOuter

@[expose] def invW (w : List ℕ) : List ℕ :=
  w.reverse.flatMap fun s => if s < 18 then [s] else [18, 18]

@[expose] def sGenP (_ : Unit := ()) : List Pr := [wordP sWordA, wordP sWordB, wordP sWordC]

@[expose] def sStep (gens : List Pr) (acc : List Pr) (p : ℕ × ℕ) : List Pr :=
  acc ++ [mulP (acc.getD p.1 oneP) (gens.getD p.2 oneP)]

@[expose] def sElems (_ : Unit := ()) : List Pr :=
  let gens := sGenP ()
  sBfs.foldl (sStep gens) [oneP]

@[expose] def cube1P (p : Pr) : Bool := mulP p (mulP p p) == oneP

@[expose] def commP (p q : Pr) : Bool := mulP p q == mulP q p

@[expose] def powsP (p : Pr) : List Pr := [oneP, p, mulP p p]

@[expose] def planeP (u v : Pr) : List Pr :=
  (powsP u).flatMap fun a => (powsP v).map fun b => mulP a b

@[expose] def isPairP (x y : Pr) : Bool :=
  x != oneP && cube1P x && cube1P y && commP x y && !((powsP x).contains y)

@[expose] def sylowCheck (_ : Unit := ()) : Bool :=
  let E := sElems ()
  let gens := sGenP ()
  decide (E.length = 243) && decide E.Nodup &&
    E.all fun x => gens.all fun g => E.contains (mulP x g)

@[expose] def classR1P (_ : Unit := ()) : List Pr := classR1.map wordP

@[expose] def classR2P (_ : Unit := ()) : List Pr := classR2.map wordP

@[expose] def rowOK (E R1 R2 : List Pr) (row : ℕ × ℕ × ℕ × List ℕ) : Bool :=
  let u := E.getD row.1 oneP
  let v := E.getD row.2.1 oneP
  let b := wordP row.2.2.2
  let bi := wordP (invW row.2.2.2)
  let P := planeP u v
  decide (row.1 < E.length) && decide (row.2.1 < E.length) && decide (row.2.2.1 < 6) &&
    isPairP u v && mulP b bi == oneP &&
    P.contains (mulP (mulP b (R1.getD row.2.2.1 oneP)) bi) &&
    P.contains (mulP (mulP b (R2.getD row.2.2.1 oneP)) bi)

@[expose] def rowsCheck (_ : Unit := ()) : Bool :=
  let E := sElems ()
  let R1 := classR1P ()
  let R2 := classR2P ()
  decide (planeRows.length = 121) && planeRows.all (rowOK E R1 R2)

@[expose] def coveredP (planes : List (List Pr)) (x y : Pr) : Bool :=
  (powsP x).contains y || !(commP x y) || planes.any fun P => P.contains x && P.contains y

@[expose] def coverCheck (_ : Unit := ()) : Bool :=
  let E := sElems ()
  let Om := (E.filter cube1P).filter fun x => x != oneP
  let planes := planeRows.map fun row => planeP (E.getD row.1 oneP) (E.getD row.2.1 oneP)
  Om.all fun x => Om.all fun y => coveredP planes x y

@[expose] def planeCoverCheck (_ : Unit := ()) : Bool := sylowCheck () && rowsCheck () && coverCheck ()

@[expose] def slpP (gens invs : List Pr) (ids : List ℕ) : Pr :=
  ids.foldl (fun acc i => mulP acc (if i % 2 = 0 then gens.getD (i / 2) oneP else invs.getD (i / 2) oneP)) oneP

@[expose] def classCheck (i : ℕ) : Bool :=
  let r1 := wordP (classR1.getD i [])
  let r2 := wordP (classR2.getD i [])
  let w1 := classG1.getD i []
  let w2 := classG2.getD i []
  let gens := (w1 ++ w2).map wordP
  let invs := (w1 ++ w2).map fun w => wordP (invW w)
  let slps := classSlp.getD i []
  r1 != oneP && r2 != oneP &&
    (w1 ++ w2).all (fun w => (wordP w).2 == 0) &&
    (w1.map wordP).all (fun s => mulP r1 s == mulP s r1) &&
    (w2.map wordP).all (fun s => mulP r2 s == mulP s r2) &&
    (w1 ++ w2).all (fun w => mulP (wordP w) (wordP (invW w)) == oneP) &&
    slps.all (fun x => decide (x.1 < 18) && slpP gens invs x.2 == (letterArr x.1, 0)) &&
    (List.range 18).all fun k => slps.any fun x => x.1 == k

@[expose] def classChecks (_ : Unit := ()) : Bool := (List.range 6).all classCheck

end HuppertD4Q2
