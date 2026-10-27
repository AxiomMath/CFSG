module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import Certificates.Data.O8p2NoDatum
public import Certificates.Data.E4QuatO8
public import Certificates.Data.E4QuatArr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover (arrTable chainTables)
open CFSG.ClassicalInvolution.O8Data CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A

@[expose] def parseNats (s : String) : List ℕ := (s.splitOn " ").filterMap String.toNat?

@[expose] def parseRows (s : String) : List (List ℕ) := (s.splitOn ";").map parseNats

@[expose] def toWord (r : List ℕ) : List ℤ := r.map Int.ofNat

@[expose] def invWord (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

@[expose] def cw (i : ℕ) (w : List ℤ) : List ℤ :=
  w.flatMap fun l => if 0 < l then (centGens.getD i []).getD (l.toNat - 1) []
    else invWord ((centGens.getD i []).getD ((-l).toNat - 1) [])

@[expose] def wordsOK (ws : List (List ℤ)) : Bool := ws.all (lettersOK 17)

@[expose] def xA (i : ℕ) : Array ℕ := mainArrs.getD i #[]

@[expose] def sqStr (i : ℕ) : String :=
  if i = 0 then sqWordsStr0 () else if i = 1 then sqWordsStr1 () else sqWordsStr2 ()

@[expose] def sqW (i : ℕ) (_ : Unit) : List (List ℤ) :=
  (parseRows (sqStr i)).map fun r => cw i (toWord r)

@[expose] def sqA (i : ℕ) (_ : Unit) : List (Array ℕ) := (sqW i ()).map omegaW

@[expose] def witW (i : ℕ) (_ : Unit) : List (List ℤ) := (E4O8Data.witWords.getD i []).map (cw i)

@[expose] def witA (i : ℕ) (_ : Unit) : List (Array ℕ) := (witW i ()).map omegaW

@[expose] def u0A (_ : Unit) : Array ℕ := omegaW (cw 0 u0Word)

@[expose] def v0A (_ : Unit) : Array ℕ := omegaW (cw 0 v0Word)

@[expose] def L0A (_ : Unit) : List (Array ℕ) := q8A 360 (xA 0) (u0A ()) (v0A ())

@[expose] def U0A (_ : Unit) : List (Array ℕ) := (L0A ()).drop 2

@[expose] def twinW (_ : Unit) : List (List ℤ) := twinWords.map (cw 0)

@[expose] def twinA (_ : Unit) : List (Array ℕ) := (twinW ()).map omegaW

@[expose] def LsA (_ : Unit) : List (List (Array ℕ)) :=
  let L := L0A ()
  L :: (twinA ()).map fun t => L.map (conjA 360 t)

@[expose] def threeW (_ : Unit) : List ℤ := cw 0 [1, 1]

@[expose] def threeA (_ : Unit) : Array ℕ := omegaW (threeW ())

@[expose] def rootA (_ : Unit) : List (Array ℕ) := (List.range 8).map fun h => genArrs[h]!

@[expose] def wsW (_ : Unit) : List (List ℤ) := (parseRows (memberWordsStr ())).map toWord

@[expose] def wsA (_ : Unit) : List (Array ℕ) := (wsW ()).map omegaW

@[expose] def sigmaA (_ : Unit) : List (List ℕ) :=
  (parseRows (memberSigmaStr ())).map fun r => r ++ r

@[expose] def treeA (_ : Unit) : List (ℕ × Bool × ℕ) :=
  (parseRows (memberTreeStr ())).map fun r => (r.getD 0 0, r.getD 1 0 == 1, r.getD 2 0)

@[expose] def kSA (i : ℕ) : Array (Array ℕ) :=
  pushWords 360 ((centGens.getD i []).map omegaW).toArray (centDerived.getD i [])

@[expose] def kBaseA (i : ℕ) : Array ℕ :=
  (((centBase.getD i []).map fun b => Fin.ofNat 360 b).map Fin.val).toArray

@[expose] def sqTablesA (n : ℕ) (r : Table) (tabs : List (List Table)) : List Table :=
  filterProducts n (fun T => tblEq n (compT n T T) r) tabs (idT n) []

@[expose] def sqTabs (i : ℕ) (_ : Unit) : List Table :=
  sqTablesA 360 (arrTable 360 (xA i)) (chainTables 360 (kSA i) (kBaseA i))

@[expose] def wordsCheck (_ : Unit) : Bool :=
  wordsOK (sqW 0 ()) && wordsOK (sqW 1 ()) && wordsOK (sqW 2 ()) && wordsOK (witW 0 ()) &&
    wordsOK (witW 1 ()) && wordsOK (witW 2 ()) &&
    wordsOK [cw 0 u0Word, cw 0 v0Word, threeW ()] && wordsOK (twinW ()) && wordsOK (wsW ())

@[expose] def k0Check (_ : Unit) : Bool :=
  eqA 360 (compA 360 (u0A ()) (u0A ())) (xA 0) && closedA 360 (L0A ()) (u0A ()) (v0A ())

@[expose] def identAt (i : ℕ) (Ls : List (List (Array ℕ))) : Bool :=
  let S := sqA i ()
  let W := witA i ()
  let ST := S.map (arrTable 360)
  (sqTabs i ()).all (fun T => ST.any (tblEq 360 T)) && W.all (fun c => commArr c (xA i)) &&
    identSqCheckA 360 (xA i) S W Ls

@[expose] def graphCheck (_ : Unit) : Bool :=
  let L := L0A ()
  let u := u0A ()
  let v := v0A ()
  let ws := wsA ()
  memberCheckA 360 (rootA ()) L u v ws (sigmaA ()) && treeCheckA 360 L (U0A ()) u v ws (treeA ()) &&
    nbrCheckA 360 L u v ws [0, 1, 3, 4] && edgeCheckA 360 L u v (ws.getD 1 (idA 360)) &&
    [1, 3, 4].all fun k => commArr (ws.getD k (idA 360)) (xA 0)

@[expose] def linkCheck (_ : Unit) : Bool :=
  let t := threeA ()
  commArr genArrs[8]! (xA 0) && commArr genArrs[9]! (xA 0) &&
    eqA 360 (compA 360 t (compA 360 t t)) (idA 360) &&
    normsA 360 (L0A ()) (u0A ()) (v0A ()) t && !commArr t (u0A ())

@[expose] def check (_ : Unit) : Bool :=
  wordsCheck () && k0Check () && identAt 0 (LsA ()) && identAt 1 [] && identAt 2 [] &&
    graphCheck () && linkCheck ()

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
