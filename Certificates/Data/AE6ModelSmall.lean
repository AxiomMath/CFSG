module

public import Certificates.Data.AE6ModelCore

public section

namespace Certificates.AE6Model

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native Certificates.S7Twin

@[expose] def sLetters : List ℕ := [0, 2, 4, 6]

@[expose] def sGens (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  sLetters.map fun i => G.getD i 1

@[expose] def sDerive : List (List ℤ) := [[-2, 3, 2], [-5, 4, 5], [-4, -2, 4, 2]]

@[expose] def sQ (_ : Unit := ()) : RawSchreierDatum 360 :=
  certificate (by decide) (sGens ()) sDerive #v[0, 2, 4, 24, 8] (by decide)

@[expose] def czLetters : List ℕ := [0, 1, 2, 4, 5, 6, 7]

@[expose] def czGens (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  czLetters.map fun i => G.getD i 1

@[expose] def czDerive : List (List ℤ) :=
  [[-3, 4, 3], [-8, 6, 8], [-6, -3, 6, 3], [-6, -9, -4, -8, -1, -8, -1, -2, 10, 1, 8, 1]]

@[expose] def czQ (_ : Unit := ()) : RawSchreierDatum 360 :=
  certificate (by decide) (czGens ()) czDerive #v[0, 2, 4, 24, 8] (by decide)

@[expose] def genTabs (_ : Unit := ()) : Array Table := ((curtisPerms ()).map toTable).toArray

@[expose] def genInvTabs (_ : Unit := ()) : Array Table :=
  ((curtisPerms ()).map fun g => toTable g⁻¹).toArray

@[expose] def zClass (_ : Unit := ()) : Array Table × Array ℕ × Array ℕ :=
  conjClosure 360 (genTabs ()) (genInvTabs ()) (toTable (z0 ())) 2000

@[expose] def spanQ (R Y : Table) : List Table :=
  let R2 := compT 360 R R
  [idT 360, R2, R, compT 360 R R2, Y, compT 360 Y R2, compT 360 R Y, compT 360 Y R]

@[expose] def twinPairs (_ : Unit := ()) : List (Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)) :=
  let K := k0Gens ()
  let x := K.getD 0 1
  let y := K.getD 1 1
  (cPerms ()).map fun c => (c * x * c⁻¹, c * y * c⁻¹)

@[expose] def twinSpans (_ : Unit := ()) : List (List Table) :=
  (twinPairs ()).map fun p => spanQ (toTable p.1) (toTable p.2)

@[expose] def cutWord : List ℕ := [1, 5, 7]

@[expose] def cutPerm (_ : Unit := ()) : Equiv.Perm (Fin 360) := aeWord (curtisPerms ()) cutWord

@[expose] def conjWords : List (List ℕ) := [[], [0], [1], [2], [4], [5], [6], [7]]

@[expose] def conjPerms (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  conjWords.map (aeWord G)

@[expose] def conjData (CT : List (Table × Table)) (X Y : Table) :
    List (Table × Table × List Table) :=
  CT.map fun c =>
    let U := conjT 360 c.1 c.2 X
    let V := conjT 360 c.1 c.2 Y
    (U, V, spanQ U V)

@[expose] def newPos (L : List (Table × Table × List Table)) : List ℕ :=
  (List.range L.length).filter fun a =>
    let u := L.getD a default
    (List.range a).all fun b =>
      let v := L.getD b default
      !(memT 360 v.2.2 u.1 && memT 360 v.2.2 u.2.1)

@[expose] def smChains (_ : Unit := ()) : Bool :=
  let S := sQ ()
  let C := czQ ()
  S.check && S.orderCertificate == 4096 && C.check && C.orderCertificate == 110592

@[expose] def smComm (_ : Unit := ()) : Bool :=
  let Z := toTable (z0 ())
  (czGens ()).all (fun g => commT 360 (toTable g) Z && sqOneT 360 (toTable g)) &&
    (sGens ()).all (fun g => commT 360 (toTable g) Z) && commT 360 (toTable (cutPerm ())) Z &&
    (conjPerms ()).all fun c => commT 360 (toTable c) Z

@[expose] def smClass (_ : Unit := ()) : Bool :=
  let c := zClass ()
  conjTreeOK 360 (genTabs ()) (genInvTabs ()) (toTable (z0 ())) c.1 c.2.1 c.2.2 &&
    keysDistinct 360 c.1.toList && c.1.size == 1575

@[expose] def smK0 (_ : Unit := ()) : Bool :=
  let K := k0Gens ()
  let x := K.getD 0 1
  let y := K.getD 1 1
  q8RelT 360 (toTable x) (toTable x⁻¹) (toTable y) (toTable y⁻¹) &&
    tblEq 360 (compT 360 (toTable x) (toTable x)) (toTable (z0 ())) && (twinPairs ()).length == 4

@[expose] def smTwins (_ : Unit := ()) : Bool :=
  let TP := twinPairs ()
  let TS := twinSpans ()
  (czGens ()).all fun g =>
    let Gt := toTable g
    let Gi := toTable g⁻¹
    TP.all fun p => TS.any fun sp =>
      memT 360 sp (conjT 360 Gt Gi (toTable p.1)) && memT 360 sp (conjT 360 Gt Gi (toTable p.2))

@[expose] def smPairs (_ : Unit := ()) : Bool :=
  let ST := allTables (sQ ())
  let Z := toTable (z0 ())
  let H := toTable (cutPerm ())
  let Hi := toTable (cutPerm ())⁻¹
  let X4 := ST.filter fun X => tblEq 360 (compT 360 X X) Z && memT 360 ST (conjT 360 Hi H X)
  let TS := twinSpans ()
  let CT := (conjPerms ()).map fun c => (toTable c, toTable c⁻¹)
  X4.all fun X => X4.all fun Y =>
    !tblEq 360 (compT 360 (compT 360 X Y) X) Y ||
      TS.any (fun sp => memT 360 sp X && memT 360 sp Y) ||
      decide (5 ≤ (newPos (conjData CT X Y)).length)

end Certificates.AE6Model
