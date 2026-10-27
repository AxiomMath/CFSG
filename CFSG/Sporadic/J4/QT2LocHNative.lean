module

public import CFSG.Sporadic.J4.QT2LocFiveNative
public import CFSG.Sporadic.J4.QT2LocNative
public import CFSG.Sporadic.J4.QTOutActNative
public import Std.Data.HashSet.Basic

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.QT

@[expose] def xiT : List Nat := wordT fiveWord

@[expose] def xiK (k : Nat) : List Nat := powT xiT k

@[expose] def cubeT (t : List Nat) : List Nat := powT t 3

@[expose] def cjT (d t : List Nat) : List Nat := compT d (compT t d)

@[expose] def letConj (ℓ : Int) (t : List Nat) : List Nat :=
  compT (letterTab ℓ) (compT t (letterTab (-ℓ)))

@[expose] def invSeedsT : List (List Nat) := tabL.filter fun t => compT t t == idT

@[expose] def closureConjT (seeds : List (List Nat)) (fuel : Nat) : Array (List Nat) :=
  Id.run do
    let mut seen : Std.HashSet (List Nat) := {}
    let mut arr : Array (List Nat) := #[]
    for s in seeds do
      if !seen.contains s then
        seen := seen.insert s
        arr := arr.push s
    let mut i := 0
    for _ in [0:fuel] do
      if i < arr.size then
        let t := arr[i]!
        for ℓ in letters do
          let u := letConj ℓ t
          if !seen.contains u then
            seen := seen.insert u
            arr := arr.push u
        i := i + 1
    return arr

@[expose] def isetT : List (List Nat) := (closureConjT invSeedsT 60000).toList

@[expose] def isetSet : Std.HashSet (List Nat) := Std.HashSet.ofList isetT

@[expose] def chkIset : Bool :=
  invSeedsT.all (fun s => isetSet.contains s) &&
    isetT.all fun t => compT t t == idT && letters.all fun ℓ => isetSet.contains (letConj ℓ t)

@[expose] def xiConj (t : List Nat) : List Nat := compT xiT (compT t (powT xiT 4))

@[expose] def xiConjs (y : List Nat) : List (List Nat) :=
  [y, xiConj y, xiConj (xiConj y), xiConj (xiConj (xiConj y)),
    xiConj (xiConj (xiConj (xiConj y)))]

@[expose] def commProd (y : List Nat) : Bool :=
  compT y (xiConj y) == compT (xiConj y) y &&
    (let c := xiConjs y
     (List.range 5).all (fun i => (List.range 5).all fun j =>
       compT (c.getD i idT) (c.getD j idT) == compT (c.getD j idT) (c.getD i idT)) &&
       c.foldr compT idT == idT)

@[expose] def subsetProds (c : List (List Nat)) : List (List Nat) :=
  c.foldr (fun x acc => acc ++ acc.map (compT x)) [idT]

@[expose] def spanT (y : List Nat) : List (List Nat) := (subsetProds (xiConjs y)).eraseDups

@[expose] def vGroups : List (List (List Nat)) :=
  isetT.foldl (fun acc y =>
    if y != idT && commProd y && !(acc.any fun G => G.contains y) then acc ++ [spanT y]
    else acc) []

@[expose] def chkV : Bool :=
  vGroups.length == 5 &&
    vGroups.all (fun G => G.length == 16 && decide G.Nodup &&
      G.all fun y => y == idT || G.all fun g => (spanT y).contains g) &&
    isetT.all fun y => !commProd y || vGroups.any fun G => G.contains y

@[expose] def duadL : List Nat := tMasks

@[expose] def chkDuad : Bool := duadL.all fun c => c != 0 && decide (c < 2048)

@[expose] def chkCaseI (k : Nat) : Bool :=
  vGroups.all fun G => isetT.all fun d =>
    !(G.all fun g => G.contains (cjT d g)) || !(G.contains (cubeT (compT (xiK k) d))) ||
      duadL.any fun c => actT (xiK k) c == c && actT d c == c && G.all fun g => actT g c == c

@[expose] def span4 (v : Nat) : List Nat :=
  let w1 := actT xiT v
  let w2 := actT xiT w1
  let w3 := actT xiT w2
  (List.range 16).map fun m =>
    (if m.testBit 0 then v else 0) ^^^ (if m.testBit 1 then w1 else 0) ^^^
      (if m.testBit 2 then w2 else 0) ^^^ (if m.testBit 3 then w3 else 0)

@[expose] def fpfL (S : List Nat) : Bool := S.all fun s => s == 0 || actT xiT s != s

@[expose] def invL (S : List Nat) : Bool := S.all fun s => S.contains (actT xiT s)

@[expose] def chkLines : Bool :=
  (List.range 2048).all fun v => v == 0 || !(fpfL (span4 v)) || (span4 v).eraseDups.length == 16

@[expose] def lines17 : List (List Nat) :=
  ((List.range 2048).filter fun v => v != 0 && fpfL (span4 v) && invL (span4 v)).map
    (fun v => ((span4 v).eraseDups).mergeSort) |>.eraseDups

@[expose] def chkCaseII (k : Nat) : Bool :=
  isetT.all fun d =>
    !(cubeT (compT (xiK k) d) == idT) ||
      duadL.any (fun c => actT (xiK k) c == c && actT d c == c) ||
      lines17.all fun S => !(S.all fun s => S.contains (actT d s)) ||
        S.all fun s => s == 0 || actT (compT (xiK k) d) s != s

@[expose] def chkAll : Bool :=
  chkIset && chkDuad && chkV && chkLines &&
    chkCaseI 1 && chkCaseI 2 && chkCaseI 3 && chkCaseI 4 &&
    chkCaseII 1 && chkCaseII 2 && chkCaseII 3 && chkCaseII 4

end CFSG.Sporadic.J4.QT2
