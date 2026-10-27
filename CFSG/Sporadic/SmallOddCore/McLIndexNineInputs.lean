module

public import CFSG.Sporadic.SmallOddCore.McLData
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.PSL3Four.Native

@[expose] def mclIndexNineU1 : List Nat :=
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1,
    2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1]

@[expose] def mclIndexNineU2 : List Nat :=
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1,
    2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1]

@[expose] def mclIndexNineU3 : List Nat :=
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2]

@[expose] def mclIndexNineUWords : List (List Nat) :=
  [mclIndexNineU1, mclIndexNineU2, mclIndexNineU3]

@[expose] def mclIndexNinePoint : Nat := 200

@[expose] def mclIndexNineX : List Nat :=
  [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2,
    2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

@[expose] def mclIndexNineY : List Nat :=
  [1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
    1]

@[expose] def mclIndexNineGens : List Table := [mclCentTbl 5, mclCentTbl 6]

@[expose] def mclIndexNineUTbls (_ : Unit := ()) : List Table :=
  mclIndexNineUWords.map fun w => wordTbl 275 mclIndexNineGens w

@[expose] def mclIndexNineXTbl (_ : Unit := ()) : Table :=
  wordTbl 275 mclIndexNineGens mclIndexNineX

@[expose] def mclIndexNineYTbl (_ : Unit := ()) : Table :=
  wordTbl 275 mclIndexNineGens mclIndexNineY

@[expose] def mclPointTab (p : Nat) : Table := Array.replicate 275 (UInt32.ofNat p)

@[expose] def mclIndexNineFixPointCheck (_ : Unit := ()) : Bool :=
  let U := mclIndexNineUTbls ()
  U.all fun u => decide (ap u mclIndexNinePoint = mclIndexNinePoint)

@[expose] def mclIndexNineFixSetCheck (_ : Unit := ()) : Bool :=
  let U := mclIndexNineUTbls ()
  (List.range 275).all fun q => q == mclIndexNinePoint || U.any fun u => decide (ap u q ≠ q)

@[expose] def mclIndexNineCommCheck (_ : Unit := ()) : Bool :=
  let U := mclIndexNineUTbls ()
  let t0 := mclCentTbl 4
  U.all fun u => tblEq 275 (compT 275 u t0) (compT 275 t0 u)

@[expose] def mclIndexNineXYFixCheck (_ : Unit := ()) : Bool :=
  let x := mclIndexNineXTbl ()
  let y := mclIndexNineYTbl ()
  decide (ap x mclIndexNinePoint = mclIndexNinePoint) &&
    decide (ap y mclIndexNinePoint = mclIndexNinePoint)

@[expose] def mclIndexNineXYCommCheck (_ : Unit := ()) : Bool :=
  let x := mclIndexNineXTbl ()
  let y := mclIndexNineYTbl ()
  let t0 := mclCentTbl 4
  tblEq 275 (compT 275 x t0) (compT 275 t0 x) &&
    tblEq 275 (compT 275 y t0) (compT 275 t0 y)

@[expose] def mclIndexNineXYOrderCheck (_ : Unit := ()) : Bool :=
  let x := mclIndexNineXTbl ()
  let y := mclIndexNineYTbl ()
  tblEq 275 (powT 275 3 x) (idT 275) && tblEq 275 (powT 275 3 y) (idT 275)

@[expose] def mclIndexNineXYMulCheck (_ : Unit := ()) : Bool :=
  let x := mclIndexNineXTbl ()
  let y := mclIndexNineYTbl ()
  tblEq 275 (compT 275 x y) (compT 275 y x)

@[expose] def mclIndexNineXNonTrivialCheck (_ : Unit := ()) : Bool :=
  let x := mclIndexNineXTbl ()
  !tblEq 275 x (idT 275)

@[expose] def mclIndexNineYNotInXCheck (_ : Unit := ()) : Bool :=
  let x := mclIndexNineXTbl ()
  let y := mclIndexNineYTbl ()
  let x2 := compT 275 x x
  !tblEq 275 y (idT 275) && !tblEq 275 y x && !tblEq 275 y x2

@[expose] def mclIndexNineOrbitWords : List (List Nat) := [
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1,
    2, 2, 2, 2],
  [2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2],
  [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2],
  [2, 2],
  [2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2],
  [2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
    2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2],
  [2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2],
  [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2],
  [2],
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 1, 2, 2, 1],
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2],
  [2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2],
  [2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2],
  [],
  [1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2],
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2],
  [2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2],
  [2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1],
  [2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2],
  [2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2],
  [2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2],
  [2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 1],
  [2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2],
  [2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1],

]

@[expose] def mclIndexNineOrbitPoints : List Nat := [
  0, 24, 26, 48, 72, 74, 83, 106, 112, 114, 131, 143,
  151, 163, 169, 176, 180, 193, 195, 196, 200, 208, 213, 219,
  227, 228, 244, 254, 260, 262, 263, 264, 270, 271, 272
]

@[expose] def mclIndexNineOrbitCheck (_ : Unit := ()) : Bool :=
  let gens := mclIndexNineGens
  let pts := mclIndexNineOrbitWords.map fun w => ap (wordTbl 275 gens w) mclIndexNinePoint
  pts == mclIndexNineOrbitPoints && pts.Nodup

@[expose] def mclIndexNinePermCheck (_ : Unit := ()) : Bool :=
  let U := mclIndexNineUTbls ()
  let x := mclIndexNineXTbl ()
  let y := mclIndexNineYTbl ()
  let gens := mclIndexNineGens
  U.all (fun u => permOK 275 u) && permOK 275 x && permOK 275 y &&
    mclIndexNineOrbitWords.all (fun w => permOK 275 (wordTbl 275 gens w))

@[expose] def mclIndexNineCentralCount (_ : Unit := ()) : Nat :=
  let U := mclIndexNineUTbls ()
  centCount 275 128 U U

@[expose] def mclIndexNineCheck (_ : Unit := ()) : Bool :=
  let U := mclIndexNineUTbls ()
  enumOK 275 128 128 U && decide (mclIndexNineCentralCount () = 2) &&
    mclIndexNinePermCheck () &&
    mclIndexNineFixPointCheck () && mclIndexNineFixSetCheck () &&
    mclIndexNineCommCheck () && mclIndexNineXYFixCheck () &&
    mclIndexNineXYCommCheck () && mclIndexNineXYOrderCheck () &&
    mclIndexNineXYMulCheck () && mclIndexNineXNonTrivialCheck () &&
    mclIndexNineYNotInXCheck () && mclIndexNineOrbitCheck ()

end CFSG.Sporadic.SmallOddCore
