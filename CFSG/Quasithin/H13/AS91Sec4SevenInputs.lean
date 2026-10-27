module

public import CFSG.Quasithin.H13.AS91Sec4SixInputs
public import CFSG.Quasithin.H13.AS91Sec4FourInputs

public section

namespace CFSG.Quasithin.H13.AS91.Two

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum CFSG.GF2Type.Smith1979.IdxFour

@[expose] def iRows : List (Array ℕ) :=
  [#[3898, 3897, 199, 200, 208, 224, 444, 380, 259, 707, 1219, 2243],
    #[1030, 1029, 7, 8, 211, 32, 1424, 1360, 448, 512, 1027, 2048]]

@[expose] def fGen : List (Array ℕ) :=
  [#[1, 2, 2564, 308, 56, 284, 64, 128, 2856, 3076, 3584, 1540],
    #[41, 42, 2604, 1307, 2576, 1331, 2624, 2688, 296, 980, 3624, 2516],
    #[41, 42, 44, 1063, 2616, 1039, 2624, 2688, 2816, 3536, 1064, 2000]]

@[expose] def fRows (i : ℕ) : List (Array ℕ) := fGen.getD i idR :: iRows

@[expose] def baseOK47 (_ : Unit := ()) : Bool :=
  let Ps := Std.HashSet.ofList (enumGrp pRows)
  let P2 := enumGrp p2Rows
  let Eb := enumGrp ebRows
  let I := enumGrp iRows
  p2Rows.all (fun p => Ps.contains p) &&
    gensOKb iRows && I.contains idR && closedCheck iRows I && I.dedup.length == 4 &&
    iRows.all (fun r => Eb.contains r && P2.contains r) &&
    Eb.all fun x => !P2.contains x || I.contains x

@[expose] def fOK47 (_ : Unit := ()) : Bool :=
  let Eb := enumGrp ebRows
  (List.range 3).all fun i =>
    gensOKb (fRows i) && (enumGrp (fRows i)).contains idR &&
      closedCheck (fRows i) (enumGrp (fRows i)) && (enumGrp (fRows i)).dedup.length == 8 &&
      (fRows i).all (fun r => Eb.contains r) &&
      (List.range 3).all fun j => i == j || !(enumGrp (fRows j)).contains (fGen.getD i idR)

@[expose] def g1List (_ : Unit := ()) : List (Array ℕ) :=
  (enumGrp gZRows).filter fun x => w1List.all fun c => w1List.contains (appN x c)

@[expose] def fLists (_ : Unit := ()) : List (List (Array ℕ)) :=
  (List.range 3).map fun i => enumGrp (fRows i)

@[expose] def conjInto (x : Array ℕ) (F F' : List (Array ℕ)) : Bool :=
  F.all fun f => F'.any fun f' => mulR x f == mulR f' x

@[expose] def gOK47 (_ : Unit := ()) : Bool :=
  let P2 := enumGrp p2Rows
  let Eb := enumGrp ebRows
  let FL := fLists ()
  (g1List ()).all fun x =>
    (FL.all fun F => FL.any fun F' => conjInto x F F') &&
      (!(FL.all fun F => conjInto x F F) || Eb.any fun e => P2.any fun p => mulR p e == x)

@[expose] def ok47 (_ : Unit := ()) : Bool := baseOK47 () && fOK47 () && gOK47 ()

end CFSG.Quasithin.H13.AS91.Two
