module

public import Certificates.Data.HuppertU38Fix.Data
public import Certificates.Data.HuppertU38Q.NoE81

public section

namespace U38Fix

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38 U38Sylow

@[expose] def isIdA (a : Array ℕ) : Bool := eqA 513 a (idA 513)

@[expose] def cubeComm (a : Array ℕ) : Bool := cubeOne a && commAt a x7

@[expose] def inXA (lev3 : Array Level) (a : Array ℕ) : Bool := siftA 513 lev3 base3 0 a

@[expose] def hCert (_ : Unit := ()) : ArrCert := enumBfs 513 hGens keyPts 500

@[expose] def fixOK (lev3 : Array Level) (c : ArrCert) : Bool :=
  c.pts.all fun a => !cubeComm a || inXA lev3 a

@[expose] def fixWit (lev3 : Array Level) (c : ArrCert) : Bool :=
  c.pts.any fun a => cubeComm a && !isIdA a && inXA lev3 a

@[expose] def fixCheck (_ : Unit := ()) : Bool :=
  let c := hCert ()
  let lev1 := rawLevels 513 strong1 base1
  let lev3 := rawLevels 513 strong3 base3
  enumOK 513 hGens keyPts c && c.pts.size == 378 &&
    allLt hGens.size (fun k => siftA 513 lev1 base1 0 hGens[k]!) &&
    allLt hGens.size (fun k => (hGens[k]!)[109]! == 109 && (hGens[k]!)[458]! == 458) &&
    x7[109]! == 109 && x7[458]! == 458 && inXA lev3 x7 && fixOK lev3 c && fixWit lev3 c

@[expose] def pw3 (x : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 513
  | 1 => x
  | _ => compA 513 x x

@[expose] def e0List (_ : Unit := ()) : List (Array ℕ) :=
  (List.range 3).flatMap fun a => (List.range 3).map fun b => compA 513 (pw3 eBar a) (pw3 fBar b)

@[expose] def uTab (P E0 hl : List (Array ℕ)) : List (Array ℕ × List (Array ℕ)) :=
  (hl.flatMap fun h => P.map fun y => compA 513 h y).map fun u => (u, E0.map fun w => compA 513 w u)

@[expose] def coverOne (T : List (Array ℕ × List (Array ℕ))) (z : Array ℕ) : Bool :=
  T.any fun p => p.2.any fun wu => eqA 513 (compA 513 p.1 z) wu

@[expose] def coverAll (T : List (Array ℕ × List (Array ℕ))) (P : List (Array ℕ)) : Bool :=
  P.all fun z => !cubeOne z || isIdA z || coverOne T z

@[expose] def toralCheck (_ : Unit := ()) : Bool :=
  let c := qCert ()
  let lev3 := rawLevels 513 strong3 base3
  let nIdx := inX c.pts lev3
  let P := nIdx.map fun i => c.pts[i]!
  let E0 := e0List ()
  let hl := idA 513 :: tHs.toList
  enumOK 513 qGens keyPts c && c.pts.size == 729 && nIdx.length == 81 &&
    validA 513 eBar && validA 513 fBar && validA 513 gRefl && allLt tHs.size (fun k => validA 513 tHs[k]!) &&
    inXA lev3 eBar && inXA lev3 fBar && inXA lev3 gRefl && allLt tHs.size (fun k => inXA lev3 tHs[k]!) &&
    cubeOne eBar && cubeOne fBar && !isIdA eBar && !isIdA fBar &&
    !eqA 513 fBar eBar && !eqA 513 fBar (compA 513 eBar eBar) && commAt eBar fBar &&
    commAt gRefl eBar && eqA 513 (compA 513 gRefl fBar) (compA 513 (compA 513 fBar fBar) gRefl) &&
    coverAll (uTab P E0 hl) P

@[expose] def u38FixAllCheck (_ : Unit := ()) : Bool := fixCheck () && toralCheck ()

end U38Fix
