module

public import Certificates.Data.CFSGNative.SmallOddCore.Check

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

inductive OddWit where
  | conj (h : Table) (ord : Nat)
  | normal (gens : List Table) (ord : Nat)

structure OddRow where
  rep : Table
  prime : Nat
  classSize : Nat
  wit : OddWit

structure ClassRow where
  rep : Table
  outer : Bool
  classSize : Nat
  centOrder : Nat
  centGens : List Table
  oddPrimes : List Nat
  odd : List OddRow

@[expose] def commTT (n : Nat) (x y : Table) : Bool := tblEq n (compT n x y) (compT n y x)

@[expose] def permOK (n : Nat) (x : Table) : Bool :=
  CFSG.Monster.B.Co2.Native.isInvA n (natArr x) (CFSG.Monster.B.Co2.Native.invCand n (natArr x))

@[expose] def involOK (n : Nat) (x : Table) : Bool := invoOK n x && !tblEq n x (idT n)

@[expose] def selOK (n : Nat) (ps : List Nat) (y : Table) : Bool :=
  !tblEq n y (idT n) && ps.any fun p => tblEq n (powT n p y) (idT n)

@[expose] def oddRowOK (n cap : Nat) (sift : Table → Bool) (t : Table) (cg cgInv : Array Table)
    (s : OddRow) : Bool :=
  permOK n s.rep && sift s.rep && commTT n s.rep t && ordTest n s.prime s.rep &&
    match s.wit with
    | .conj h ord => permOK n h && sift h && commTT n h t && invOK n h (invT n h) &&
        ord % 2 == 0 && 0 < ord && ordTest n ord (compT n s.rep (conjT n h (invT n h) s.rep))
    | .normal gs _ =>
        let q := conjClosureH n cg cgInv s.rep cap
        let e := mulClosureH n gs.toArray cap
        conjTreeOK n cg cgInv s.rep q.1 q.2.1 q.2.2 &&
          gs.all (fun g => permOK n g && memT n q.1 g) &&
          mulTreeOK n gs.toArray e.1 e.2.1 e.2.2 && e.1.any (involOK n)

abbrev Closure := Array Table × Array Nat × Array Nat

@[expose] def classOK (n NP cap : Nat) (pg pgInv : Array Table) (sift : Table → Bool) (u : Table)
    (r : ClassRow) (o : Closure) : Bool :=
  let t := r.rep
  let cg := r.centGens.toArray
  let cgInv := cg.map (invT n)
  let C := mulClosureH n cg cap
  let queues := r.odd.map fun s => (s, conjClosureH n cg cgInv s.rep cap)
  permOK n t && involOK n t && (if r.outer then !sift t && sift (compT n t u) else sift t) &&
    conjTreeOK n pg pgInv t o.1 o.2.1 o.2.2 && hkeysDistinct n o.1.toList &&
    o.1.size == r.classSize &&
    cg.all (fun c => permOK n c && sift c && commTT n c t && invOK n c (invT n c)) &&
    mulTreeOK n cg C.1 C.2.1 C.2.2 && hkeysDistinct n C.1.toList && C.1.size == r.centOrder &&
    r.classSize * r.centOrder == NP &&
    r.odd.all (oddRowOK n cap sift t cg cgInv) &&
    queues.all (fun q => conjTreeOK n cg cgInv q.1.rep q.2.1 q.2.2.1 q.2.2.2) &&
    C.1.all (fun y => !selOK n r.oddPrimes y || queues.any (fun q => memT n q.2.1 y))

@[expose] def sylowOK (n cap : Nat) (pg pgInv : Array Table) (sift : Table → Bool) (u : Table)
    (sylowGens : List Table) (sylowOrder : Nat) : Bool :=
  let uInv := invT n u
  let sg := sylowGens.toArray
  let syl := mulClosureH n sg cap
  permOK n u && involOK n u && !sift u && invOK n u uInv &&
    pg.all (fun g => sift g) && pg.size == pgInv.size &&
    allIn 0 pg.size (fun l => invOK n pg[l]! pgInv[l]!) &&
    pg.all (fun g => sift (conjT n u uInv g)) &&
    sg.all (fun x => permOK n x && invOK n x (invT n x) && (sift x || sift (compT n x u))) &&
    mulTreeOK n sg syl.1 syl.2.1 syl.2.2 && closedOK n (sg ++ sg.map (invT n)) syl.1 &&
    hkeysDistinct n syl.1.toList && syl.1.size == sylowOrder

@[expose] def coverOK (n cap : Nat) (u : Table) (sylowGens : List Table)
    (rowsO : List (ClassRow × Closure)) : Bool :=
  let uInv := invT n u
  let syl := mulClosureH n sylowGens.toArray cap
  syl.1.all (fun s => !involOK n s || rowsO.any (fun p => memT n p.2.1 s)) &&
    rowsO.all (fun p => rowsO.any (fun q => memT n q.2.1 (conjT n u uInv p.1.rep)))

@[expose] def centDataOK (n NP cap : Nat) (pg pgInv : Array Table) (sift : Table → Bool)
    (u : Table) (sylowGens : List Table) (sylowOrder : Nat) (rows : List ClassRow) : Bool :=
  let rowsO := rows.map fun r => (r, conjClosureH n pg pgInv r.rep cap)
  sylowOK n cap pg pgInv sift u sylowGens sylowOrder &&
    rowsO.all (fun p => classOK n NP cap pg pgInv sift u p.1 p.2) &&
    coverOK n cap u sylowGens rowsO

end CFSG.Sporadic.SmallOddCore
