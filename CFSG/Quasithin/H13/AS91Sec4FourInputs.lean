module

public import CFSG.Quasithin.H13.AS91Sec4FiveInputs

public section

namespace CFSG.Quasithin.H13.AS91.Two

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum CFSG.GF2Type.Smith1979.IdxFour

@[expose] def gZRows : List (Array ℕ) :=
  [#[1498, 1497, 3619, 556, 1268, 1567, 855, 919, 1784, 2312, 2515, 472],
    #[2293, 2294, 1735, 3587, 3376, 303, 1443, 1379, 1819, 3832, 308, 2756]]

@[expose] def p2Rows : List (Array ℕ) :=
  [#[14, 13, 7, 11, 16, 32, 896, 832, 448, 704, 1024, 2048],
    #[822, 821, 196, 203, 19, 35, 3724, 3660, 451, 515, 1216, 2240],
    #[1030, 1029, 7, 8, 211, 32, 1424, 1360, 448, 512, 1027, 2048],
    #[2053, 2054, 7, 8, 16, 227, 2400, 2464, 448, 512, 1024, 2051]]

@[expose] def perpWit : List ℕ := [4, 24]

@[expose] def w5 (_ : Unit := ()) : List ℕ :=
  (w1Orbit ()).filter fun m => m.testBit 3 && m.testBit 192 && m.testBit 195

@[expose] def codesOf (m : ℕ) : List ℕ := (List.range 4096).filter m.testBit

@[expose] def mapsInto (x : Array ℕ) (m : ℕ) (cs : List ℕ) : Bool :=
  cs.all fun c => m.testBit (appN x c)

@[expose] def zGrpOK44 (_ : Unit := ()) : Bool :=
  let X := enumGrp gZRows
  let Xs := Std.HashSet.ofList X
  let P := enumGrp p2Rows
  let St := Std.HashSet.ofList (enumGrp (stab1Gens ()))
  gensOKb gZRows && gensOKb p2Rows && gZRows.all (fun g => St.contains g && appN g 192 == 192) &&
    appN ((stab1Gens ()).getD 4 idR) 192 != 192 &&
    X.contains idR && closedCheck gZRows X && X.dedup.length == 1920 &&
    P.contains idR && closedCheck p2Rows P && P.dedup.length == 16 &&
    p2Rows.all (fun p => Xs.contains p) &&
    P.all (fun x => P.all fun y => mulR x y == mulR y x) && P.all (fun x => mulR x x == idR)

@[expose] def zW5OK44 (_ : Unit := ()) : Bool :=
  let X := enumGrp gZRows
  let Ps := Std.HashSet.ofList (enumGrp p2Rows)
  let WC := (w5 ()).map fun m => (m, codesOf m)
  (w5 ()).length == 5 &&
    p2Rows.all (fun p => WC.all fun mc => mapsInto p mc.1 mc.2) &&
    X.all (fun x => !(WC.all fun mc => mapsInto x mc.1 mc.2) || Ps.contains x)

@[expose] def zPerpOK44 (_ : Unit := ()) : Bool :=
  (enumGrp p2Rows).all fun x => !(perpWit.all fun c => appN x c == c) || x == idR

@[expose] def ok44 (_ : Unit := ()) : Bool := zGrpOK44 () && zW5OK44 () && zPerpOK44 ()

end CFSG.Quasithin.H13.AS91.Two
