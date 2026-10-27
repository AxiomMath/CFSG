module

public import Certificates.Data.GSThmBCatalog7SuzCS
public import CFSG.Sporadic.Recognition.SuzMultiplierInputs
public import Certificates.Data.CFSGNative.F3.Basic
public import Certificates.Data.CFSGNative.F3.Conj
public meta import Certificates.Data.GSThmBCatalog7SuzCS
public meta import CFSG.Sporadic.Recognition.SuzMultiplierInputs
public meta import Certificates.Data.CFSGNative.F3.Basic
public meta import Certificates.Data.CFSGNative.F3.Conj
public meta import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.Certificates.CosetTableShort
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs
public import CFSG.Sporadic.Presentation.Common
public meta import CFSG.Sporadic.Presentation.Common

public section

namespace CFSG.ComponentClassification.GSThmB.CF24

open CFSG.F3.Native CFSG.Sporadic.Recognition.SuzMultiplier CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.Tits CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.SuzOddCore
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.CatFactsL4U4.SuzCS CFSG.PSL3Four.Native
  CFSG.Sporadic.Bridge.SuzGPL.Native

@[expose] def cf24AText : String :=
  "1     3    12    12\n\
   121200112020\n\
   112111102110\n\
   020201122010\n\
   001110010002\n\
   222020100112\n\
   210012002101\n\
   220221021122\n\
   012011112200\n\
   021220012212\n\
   102221210120\n\
   012222210001\n\
   222112011021"

@[expose] def cf24BText : String :=
  "1     3    12    12\n\
   001000000000\n\
   112000000000\n\
   202000000000\n\
   000010000000\n\
   121220000000\n\
   000000100000\n\
   000000001000\n\
   000000000100\n\
   000001000000\n\
   000001121200\n\
   011212110210\n\
   011210201001"

@[expose] def cf24A : Array V := rowsOf 12 cf24AText

@[expose] def cf24B : Array V := rowsOf 12 cf24BText

@[expose] def cf24AB (z : ℤ) : Array V :=
  if z = 1 then cf24A else if z = -1 then powM 12 cf24A 3 else if z = 2 then cf24B
  else powM 12 cf24B 2

@[expose] def cf24WordM (w : List ℤ) : Array V :=
  w.foldr (fun l X => mul 12 (cf24AB l) X) (idM 12)

@[expose] def cf24EvalM (E Ei : ℕ → Array V) (w : List (Fin gcS × Bool)) : Array V :=
  w.foldr (fun l X => mul 12 (if l.2 then E l.1.val else Ei l.1.val) X) (idM 12)

@[expose] def cf24Ys : Array (Array V) := Array.ofFn (n := 7) fun k => cf24WordM imgWords[k.val]!

@[expose] def cf24Yis : Array (Array V) :=
  Array.ofFn (n := 7) fun k => cf24WordM (invZ imgWords[k.val]!)

@[expose] def cf24Es : Array (Array V) :=
  Array.ofFn (n := gcS) fun i =>
    cf24EvalM (fun k => cf24Ys[k]!) (fun k => cf24Yis[k]!) (suzCommWord i)

@[expose] def cf24Eis : Array (Array V) :=
  Array.ofFn (n := gcS) fun i =>
    cf24EvalM (fun k => cf24Ys[k]!) (fun k => cf24Yis[k]!) (FreeGroup.invRev (suzCommWord i))

@[expose] def cf24XCodes : List ℕ :=
  [4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0,
    2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6,
    4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2,
    4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12,
    5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0,
    2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 10, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6,
    4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 11, 4, 0, 2, 10, 12, 6, 2, 0, 2,
    4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12,
    10]

@[expose] def cf24YCodes : List ℕ :=
  [13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5,
    3, 1, 3, 7, 13, 11, 3, 1, 5, 8, 2, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3,
    5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 3, 9, 13, 7, 3, 1, 5, 7, 3, 5,
    1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1,
    5, 8, 2, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7,
    9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 3, 9, 13, 3, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7,
    11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 2, 12, 13, 7, 3,
    1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3,
    7, 13, 11, 3, 1, 5, 13, 3, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4,
    2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4,
    6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 4,
    4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2,
    0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4,
    2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 10, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4,
    6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 11,
    4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2,
    0, 4, 2, 6, 4, 0, 2, 6, 12, 10, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6,
    4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2,
    4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12,
    4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0,
    2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6,
    4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 10, 4, 0, 2, 10, 12, 6, 2, 0, 2,
    4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12,
    11, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2,
    0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 10, 2, 12, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6,
    4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 13, 3, 4, 0, 2, 10,
    12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6,
    4, 0, 2, 6, 12, 2, 12, 8, 2, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2,
    12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 3, 9, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4,
    6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 8,
    2, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0,
    2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 3, 9, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8,
    6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 4, 4, 0, 2, 10, 12, 6, 2, 0,
    2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6,
    12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6,
    2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6,
    8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2,
    0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2,
    6, 12, 10, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4,
    6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 11, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4,
    6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 10, 4, 4, 0, 2, 10, 12,
    6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4,
    0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10,
    6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2,
    6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10,
    12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6,
    4, 0, 2, 6, 12, 10, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2,
    10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 11, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6,
    4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 10, 13, 7,
    3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1,
    3, 7, 13, 11, 3, 1, 5, 8, 2, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7,
    9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 3, 9, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3,
    1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 8,
    2, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7,
    5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 3, 9, 13, 3, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11,
    3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 2, 12, 13, 7, 3, 1,
    5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7,
    13, 11, 3, 1, 5, 13, 3]

@[expose] def cf24X : List (Fin gcS × Bool) := suzW cf24XCodes

@[expose] def cf24Y : List (Fin gcS × Bool) := suzW cf24YCodes

@[expose] def cf24C : List (Fin gcS × Bool) := commWord cf24X cf24Y

@[expose] def cf24MatCheckOf (E Ei : ℕ → Array V) : Bool :=
  (List.range gcS).all (fun i => canonM 12 (E i) && canonM 12 (Ei i) &&
      eqM 12 (mul 12 (E i) (Ei i)) (idM 12) && eqM 12 (mul 12 (Ei i) (E i)) (idM 12)) &&
    suzCover.all (fun w => eqM 12 (cf24EvalM E Ei w) (idM 12)) &&
    eqM 12 (cf24EvalM E Ei suzR3) (idM 12) &&
    canonM 12 (cf24EvalM E Ei (suzW [6, 6])) && !eqM 12 (cf24EvalM E Ei (suzW [6, 6])) (idM 12) &&
    canonM 12 (cf24EvalM E Ei cf24C) && !eqM 12 (cf24EvalM E Ei cf24C) (idM 12)

@[noinline, expose] def cf24MatCheck : Bool :=
  let Es := cf24Es
  let Eis := cf24Eis
  cf24MatCheckOf (fun i => Es[i]!) (fun i => Eis[i]!)

@[expose] def cf24EllArrs : Array (Array ℕ) := Array.ofFn (n := 5) fun j =>
  compA 1782 (compA 1782 (compA 1782 (invInnerGenArrs 0)[1]! (invInnerGenArrs 0)[j.val + 2]!)
    (invCand 1782 (invInnerGenArrs 0)[1]!)) (invCand 1782 (invInnerGenArrs 0)[j.val + 2]!)

@[expose] def cf24XP : List ℤ := [-5, 1, -2, -1, -5]

@[expose] def cf24YP : List ℤ := [2, -5, -1, -5, 1, -2]

@[expose] def cf24O1 : List ℕ :=
  [6, 35, 60, 73, 106, 128, 135, 156, 167, 171, 214, 238, 247, 280, 282, 299, 300, 301, 313, 321,
    333, 342, 348, 352, 360, 390, 421, 426, 430, 449, 475, 478, 494, 531, 559, 567, 577, 625, 633,
    645, 656, 672, 673, 689, 691, 701, 720, 748, 752, 759, 760, 770, 784, 805, 828, 849, 853, 859,
    871, 874, 910, 943, 966, 967, 969, 973, 983, 985, 999, 1001, 1004, 1048, 1064, 1066, 1077, 1099,
    1101, 1117, 1124, 1127, 1128, 1148, 1170, 1187, 1199, 1203, 1214, 1224, 1240, 1247, 1248, 1258,
    1259, 1262, 1268, 1273, 1312, 1341, 1343, 1349, 1356, 1381, 1386, 1389, 1405, 1441, 1450, 1452,
    1455, 1481, 1489, 1496, 1502, 1521, 1524, 1539, 1540, 1657, 1658, 1698]

@[expose] def cf24InO1 (x : ℕ) : Bool := cf24O1.contains x

@[expose] def cf24XArr : Array ℕ := wordArr 1782 suzGenArrs (zword cf24X)

@[expose] def cf24YArr : Array ℕ := wordArr 1782 suzGenArrs (zword cf24Y)

@[noinline, expose] def cf24PermCheck : Bool :=
  allLt 7 (fun k => isInvA 1782 (invInnerGenArrs 0)[k]! (invCand 1782 (invInnerGenArrs 0)[k]!)) &&
    allPermsOK 1782 cf24EllArrs &&
    lettersOK gcS (zword cf24X) && lettersOK gcS (zword cf24Y) &&
    lettersOK 5 cf24XP && lettersOK 5 cf24YP &&
    eqA 1782 cf24XArr (wordArr 1782 cf24EllArrs cf24XP) &&
    eqA 1782 cf24YArr (wordArr 1782 cf24EllArrs cf24YP) &&
    eqA 1782 (compA 1782 cf24XArr cf24YArr) (compA 1782 cf24YArr cf24XArr) &&
    allBelow 5 (fun j => allBelow 1782 fun x => cf24InO1 (cf24EllArrs[j]!)[x]! == cf24InO1 x) &&
    allBelow 5 (fun j => eqA 1782 (compA 1782 betaArr cf24EllArrs[j]!)
      (compA 1782 cf24EllArrs[j]! betaArr)) &&
    cf24InO1 6 && !cf24InO1 (tArr 0)[6]! && !cf24InO1 betaArr[6]! && !cf24InO1 tBetaArr[6]!

end CFSG.ComponentClassification.GSThmB.CF24
