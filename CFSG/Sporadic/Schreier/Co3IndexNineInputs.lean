module

public import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.Co3Arrays
public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

@[expose] def co3IndexNineYList : List Nat :=
  [28, 43, 55, 141, 144, 158, 168, 173, 232, 242, 253, 269]

@[expose] def co3IndexNineMTbls (_ : Unit := ()) : Array Table :=
  (co3MArrs.extract 0 7).map fun a => a.map UInt32.ofNat

@[expose] def co3IndexNineTTbls (_ : Unit := ()) : Array Table :=
  (co3TArrs.extract 0 8).map fun a => a.map UInt32.ofNat

@[expose] def co3IndexNineGensOf (M : Array Table) : List Table :=
  M.toList ++ (M.toList.map (invT 276))

@[expose] def co3IndexNineXWord : List Nat := [9, 7, 13, 7, 10, 13, 5, 4, 10]

@[expose] def co3IndexNineYWord : List Nat := [8, 12, 14, 14, 6, 9, 13, 5]

@[expose] def co3IndexNineXTbl (M : Array Table) : Table :=
  wordTbl 276 (co3IndexNineGensOf M) co3IndexNineXWord

@[expose] def co3IndexNineYTbl (M : Array Table) : Table :=
  wordTbl 276 (co3IndexNineGensOf M) co3IndexNineYWord

@[expose] def co3IndexNineOrbit (_ : Unit := ()) : Array (List Nat) × Array Nat × Array Nat :=
  CFSG.Sporadic.Schreier.Co3.Native.hashSearch (co3MArrs.extract 0 7)
    co3IndexNineYList 315

@[expose] def co3IndexNineFixCount (O : Array (List Nat) × Array Nat × Array Nat) : Nat :=
  (O.1.toList.filter fun s =>
    (co3TArrs.extract 0 8).all fun g => imgSorted g s == s).length

@[expose] def co3IndexNinePermCheck (_ : Unit := ()) : Bool :=
  let M := co3IndexNineMTbls ()
  let T := co3IndexNineTTbls ()
  (co3IndexNineGensOf M).all (fun g => permOK 276 g && invOK 276 g (invT 276 g)) &&
    T.toList.all (fun g => permOK 276 g)

@[expose] def co3IndexNineYFixCheck (_ : Unit := ()) : Bool :=
  (co3TArrs.extract 0 8).all fun g => imgSorted g co3IndexNineYList == co3IndexNineYList

@[expose] def co3IndexNineXYCheck (M : Array Table) : Bool :=
  let X := co3IndexNineXTbl M
  let Y := co3IndexNineYTbl M
  let x2 := compT 276 X X
  [permOK 276 X, permOK 276 Y, tblEq 276 (powT 276 3 X) (idT 276),
    tblEq 276 (powT 276 3 Y) (idT 276), !tblEq 276 X (idT 276),
    tblEq 276 (compT 276 X Y) (compT 276 Y X), !tblEq 276 Y (idT 276), !tblEq 276 Y X,
    !tblEq 276 Y x2, imgSorted (natArr X) co3IndexNineYList == co3IndexNineYList,
    imgSorted (natArr Y) co3IndexNineYList == co3IndexNineYList].all id

@[expose] def co3IndexNineCheck (_ : Unit := ()) : Bool :=
  let M := co3IndexNineMTbls ()
  let O := co3IndexNineOrbit ()
  [co3IndexNinePermCheck (), co3IndexNineYFixCheck (), co3IndexNineXYCheck M,
    O.1.size == 315,
    translatesOK (co3MArrs.extract 0 7) co3IndexNineYList O.1 O.2.1 O.2.2,
    CFSG.Sporadic.Schreier.Co3.Native.keysSortedOK O.1,
    decide (co3IndexNineFixCount O = 1)].all id

end CFSG.Sporadic.Schreier.Co3
