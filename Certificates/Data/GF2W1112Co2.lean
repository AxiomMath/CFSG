module

public import Certificates.Data.CFSGNative.GF2W1112.Spin
public import Certificates.Data.CFSGNative.GF2W1112.Irr
public import Certificates.Data.CFSGNative.Co2.Data

public section

namespace CFSG.GF2W1112

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2.Native CFSG.Sporadic.Th.Native
  CFSG.Perm.Native

@[expose] def w12Co2N : Nat := 4194304

@[expose] def w12Co2QRows : Array Nat := #[1, 2, 4, 7, 8, 63, 82, 127, 255, 104, 1177, 2709, 5111, 438, 28308, 24128, 2357, 111011, 290128, 172992, 24380, 326320]

@[expose] def w12AddRows22 (X Y : Array Nat) : Array Nat :=
  Array.ofFn (n := 22) fun i => (X[i.val]?.getD 0) ^^^ (Y[i.val]?.getD 0)

@[expose] def w12Co2F0Rows (_ : Unit := ()) : Array Nat :=
  w12AddRows22 w12Co2QRows (transposeRows 22 w12Co2QRows)

@[expose] def w12Co2Rep (i : Nat) : Nat := if i == 0 then 40 else if i == 1 then 65536 else 8

@[expose] def w12Co2OrbLen (i : Nat) : Nat :=
  if i == 0 then 2300 else if i == 1 then 46575 else 2049300

@[expose] def w12Co2Words (i : Nat) : List (List Bool) :=
  if i == 0 then [
    [false, false, false, false, true, false, false, false, false, true, false, true, false],
    [false, false, true, false, false, false, false, false, false, false, false],
    [true, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false],
    [false, true, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, true, false, true, false, false, false, false]]
  else if i == 1 then [
    [false, false, false, false, true, false],
    [false, false, false, false, false, false, false, false, true, false, false],
    [false, false, true, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false],
    [true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, true],
    [false, true, false, false, false, false, true, false, true, false, false, false, false]]
  else [
    [false, false, false, false, true, false],
    [false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false],
    [true, false, false, false, false, true, false, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true],
    [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, true, false, true, false, true, false, false, true, false, false, false, false],
    [true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, true],
    [true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true]]

@[expose] def w12WordRows (rowsA rowsB : Array Nat) (w : List Bool) : Array Nat :=
  w.foldl (fun acc b => mulRows 22 acc (if b then rowsA else rowsB)) (idRows 22)

@[expose] def w12Co2RowsA (_ : Unit := ()) : Array Nat := (co2Data ()).rowsA

@[expose] def w12Co2RowsB (_ : Unit := ()) : Array Nat := (co2Data ()).rowsB

@[expose] def w12Co2QT (_ : Unit := ()) : Array Nat := transposeRows 22 w12Co2QRows

@[expose] def w12Co2FT (_ : Unit := ()) : Array Nat := transposeRows 22 (w12Co2F0Rows ())

@[expose] def w12Co2GenRows (i : Nat) (_ : Unit := ()) : Array (Array Nat) :=
  let rA := w12Co2RowsA ()
  let rB := w12Co2RowsB ()
  ((w12Co2Words i).map fun w => w12WordRows rA rB w).toArray

@[expose] def w12Co2Gens (i : Nat) (_ : Unit := ()) : Array (Array Nat) :=
  (w12Co2GenRows i ()).map (transposeRows 22)

@[expose] def w12Co2Orb (i : Nat) (_ : Unit := ()) : VOrbit :=
  vOrbitBFS 22 (co2Data ()).colsA (co2Data ()).colsB (w12Co2Rep i) (w12Co2OrbLen i)

@[expose] def w12Co2Pos (i : Nat) (_ : Unit := ()) : Array UInt32 :=
  posTable 22 (w12Co2Orb i ()).pts

@[expose] def w12Co2OrbitCheck (i : Nat) (_ : Unit := ()) : Bool :=
  let O := w12Co2Orb i ()
  let n := w12Co2OrbLen i
  let ls : Array Table := #[O.alpha, O.beta]
  let T := treeBFS n 0 ls #[0, 1]
  vOrbitOK 22 n (co2Data ()).colsA (co2Data ()).colsB O && O.pts[0]! == w12Co2Rep i &&
    T.pts.size == n && Perm.Native.treeOK n 0 T ls #[0, 1]

@[expose] def w12Co2CoverCheck (_ : Unit := ()) : Bool :=
  let qt := w12Co2QT ()
  let O0 := w12Co2Orb 0 ()
  let O1 := w12Co2Orb 1 ()
  let O2 := w12Co2Orb 2 ()
  let p0 := posTable 22 O0.pts
  let p1 := posTable 22 O1.pts
  let p2 := posTable 22 O2.pts
  w12AllLoop (fun x => x == 0 || w12QN 22 qt x || w12InPts O0.pts p0 2300 x ||
    w12InPts O1.pts p1 46575 x || w12InPts O2.pts p2 2049300 x) w12Co2N 0

@[expose] def w12Co2InvQ (useB : Bool) (_ : Unit := ()) : Bool :=
  let qt := w12Co2QT ()
  let cols := if useB then (co2Data ()).colsB else (co2Data ()).colsA
  w12AllLoop (fun x => w12QN 22 qt (vecMulN 22 cols x) == w12QN 22 qt x) w12Co2N 0

@[expose] def w12Co2FNondeg (_ : Unit := ()) : Bool :=
  let ft := w12Co2FT ()
  w12AllLoop (fun x => x == 0 || !(vecMulN 22 ft x == 0)) w12Co2N 0

@[expose] def w12Co2NoDualFixed (_ : Unit := ()) : Bool :=
  let rA := w12Co2RowsA ()
  let rB := w12Co2RowsB ()
  w12AllLoop (fun l => l == 0 || !(vecMulN 22 rA l == l) || !(vecMulN 22 rB l == l)) w12Co2N 0

@[expose] def w12Co2DualFixH1 (_ : Unit := ()) : Bool :=
  let lam0 := vecMulN 22 (w12Co2FT ()) (w12Co2Rep 0)
  let gr := w12Co2GenRows 0 ()
  w12AllLoop (fun l => l == 0 || l == lam0 || gr.any (fun R => !(vecMulN 22 R l == l))) w12Co2N 0

@[expose] def w12Co2RepsOK (_ : Unit := ()) : Bool :=
  let qt := w12Co2QT ()
  (List.range 3).all fun i =>
    w12Co2Rep i != 0 && !w12QN 22 qt (w12Co2Rep i) && decide (w12Co2Rep i < w12Co2N)

@[expose] def w12Co2GensFix (i : Nat) (_ : Unit := ()) : Bool :=
  (w12Co2Gens i ()).all fun g => vecMulN 22 g (w12Co2Rep i) == w12Co2Rep i

@[expose] def w12Co2IrrCheck (_ : Unit := ()) : Bool :=
  w12Irr 22 (w12Co2Gens 0 ()) (w12Co2FT ()) (w12Co2Rep 0) w12Co2N 21

@[expose] def w12Co2PairCheck (_ : Unit := ()) : Bool :=
  let ft := w12Co2FT ()
  !w12BN 22 ft 1 (w12Co2Rep 0) && !w12BN 22 ft 128 (w12Co2Rep 0) && w12BN 22 ft 1 128

@[expose] def w12Co2SpinCheck (i : Nat) (_ : Unit := ()) : Bool :=
  let O0 := w12Co2Orb 0 ()
  w12Check 22 (w12Co2Gens i ()) (w12Co2QT ()) (w12Co2FT ()) O0.pts (w12Co2Pos 0 ()) 2300
    (w12Co2Rep i) w12Co2N

end CFSG.GF2W1112
