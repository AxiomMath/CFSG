module

public import CFSG.RankThree.Native.HSMcLSmallData
public import Certificates.Data.DcSub
public import Certificates.Data.DcRank

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank
open CFSG.RankThree.Native (hs100Arr)

@[expose] def ta : Array Nat := hs100Arr 0

@[expose] def tb : Array Nat := hs100Arr 1

@[expose] def invT (s : Array Nat) : Array Nat :=
  (List.range s.size).foldl (fun r i => r.set! (s.getD i 0) i) (Array.replicate s.size 0)

@[expose] def AB : Array (Array Nat) := #[ta, tb, invT ta, invT tb]

@[expose] def B100 : List Nat := List.range 100

@[expose] def sWords : List (List Nat) := [[0, 1, 0, 3, 3, 0, 3, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 3, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 3], [0, 3, 0, 1, 1, 0, 1, 1, 0, 3, 3, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 1, 1, 0, 3, 3, 0, 3, 3, 0, 1, 0], [0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0, 3, 0, 3, 0, 3, 0, 3]]

@[expose] def s5Words : List (List Nat) := [[0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 3, 0, 3, 3, 0, 1, 0, 3, 0, 3, 3, 0, 3, 3, 0, 3, 0, 1, 1, 0, 1], [1, 1, 0, 1, 0, 3, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 3, 3], [0, 3, 3, 0, 1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 0, 3, 3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1]]

@[expose] def mWords : List (List Nat) := [[3, 0, 1, 1, 0, 3, 3, 0, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 3, 0, 1, 1, 0, 1, 0, 3], [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 3, 0, 1, 1, 0, 3, 0, 1, 0, 3, 3]]

@[expose] def kWords : List (List Nat) := [[3, 0, 1, 0, 1, 1, 0, 3, 0, 3, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3], [1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0]]

@[expose] def tabsOf (ws : List (List Nat)) : Array (Array Nat) := (ws.map (tabW 100 AB)).toArray

@[expose] def sTabs : Array (Array Nat) := tabsOf sWords

@[expose] def s5Tabs : Array (Array Nat) := tabsOf s5Words

@[expose] def mTabs : Array (Array Nat) := tabsOf mWords

@[expose] def kTabs : Array (Array Nat) := tabsOf kWords

@[expose] def enumTabs (G : Array (Array Nat)) (e : Array Nat × Array Nat) (N : Nat) : Array (Array Nat) :=
  let PA := (Array.range 100).map (ptsArr G e.1 e.2 N)
  (Array.range N).map fun k => PA.map fun A => A.getD k 0

@[expose] def sElems : Array (Array Nat) := enumTabs sTabs (bfsEnumL 100 B100 sTabs 600) 512

@[expose] def s5Elems : Array (Array Nat) := enumTabs s5Tabs (bfsEnumL 100 B100 s5Tabs 200) 125

@[expose] def mElems : Array (Array Nat) := enumTabs mTabs (bfsEnumL 100 B100 mTabs 12000) 11520

@[expose] def conjT (g gi t : Array Nat) : Array Nat := compT g (compT t gi)


@[expose] def commT (s t : Array Nat) : Bool :=
  (List.range 100).all fun q => img s (img t q) == img t (img s q)

@[expose] def invSeeds : List (Array Nat) := sElems.toList.filter (isInvT 100)

@[expose] def closeInv (seeds : List (Array Nat)) (cap : Nat) : Array (Array Nat) := Id.run do
  let mut seen : Std.HashSet (Array Nat) := ∅
  let mut lst : Array (Array Nat) := #[]
  for s in seeds do
    if !seen.contains s then
      seen := seen.insert s
      lst := lst.push s
  let mut i := 0
  for _ in [0:cap] do
    if i < lst.size then
      let t := lst[i]!
      for l in [0:2] do
        let t2 := conjT (AB.getD l #[]) (AB.getD (l + 2) #[]) t
        if !seen.contains t2 then
          seen := seen.insert t2
          lst := lst.push t2
      i := i + 1
  return lst

@[expose] def invList : List (Array Nat) := (closeInv invSeeds 30000).toList

@[expose] def invSet : Std.HashSet (Array Nat) := Std.HashSet.ofList invList

@[expose] def invOK : Bool :=
  let ia := invT ta
  let ib := invT tb
  invSeeds.all (fun t => invSet.contains t) &&
    invList.all fun t =>
      invSet.contains (conjT ta ia t) && invSet.contains (conjT tb ib t) &&
        invSet.contains (conjT ia ta t) && invSet.contains (conjT ib tb t)

@[expose] def degOK : Bool :=
  s5Elems.toList.all fun y =>
    y == idT 100 ||
      (let Iy := invList.filter (commT y)
       Iy.all fun e => (Iy.filter fun e' => e' != e && commT e' e).length ≤ 13)

@[expose] def conj5 (y yi e : Array Nat) : List (Array Nat) :=
  let c1 := conjT y yi e
  let c2 := conjT y yi c1
  let c3 := conjT y yi c2
  let c4 := conjT y yi c3
  [e, c1, c2, c3, c4]

@[expose] def pwDistinct : List (Array Nat) → Bool
  | [] => true
  | x :: l => l.all (fun y => x != y) && pwDistinct l

@[expose] def pwComm : List (Array Nat) → Bool
  | [] => true
  | x :: l => l.all (fun y => commT x y) && pwComm l

@[expose] def subsetProds : List (Array Nat) → List (Array Nat)
  | [] => [idT 100]
  | t :: l => let r := subsetProds l; r ++ r.map (compT t)

@[expose] def fixPts (es : List (Array Nat)) : List Nat :=
  (List.range 100).filter fun x => es.all fun t => img t x == x

@[expose] def F0 : List Nat := [0, 1, 5, 21, 39, 50, 53, 61]

@[expose] def bfsF (cap : Nat) : Array Nat × Array Nat := Id.run do
  let mut sets : Array (List Nat) := #[F0]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet (List Nat) := (∅ : Std.HashSet (List Nat)).insert F0
  let mut i := 0
  for _ in [0:cap] do
    if i < sets.size then
      let s := sets[i]!
      for t in [0:4] do
        let s' := (s.map (img (AB.getD t #[]))).mergeSort fun a b => decide (a ≤ b)
        if !seen.contains s' then
          seen := seen.insert s'
          sets := sets.push s'
          par := par.push i
          lab := lab.push t
      i := i + 1
  return (par, lab)

@[expose] def treeF : Array Nat × Array Nat := bfsF 4000

@[expose] def maskOf (l : List Nat) : List Bool := (List.range 100).map fun x => l.contains x

@[expose] def orbRows (N : Nat) (PA : List (Array Nat)) : List (List Bool) :=
  (List.range N).map fun k => maskOf (PA.map fun A => A.getD k 0)

@[expose] def orbF : List (List Bool) := orbRows 3850 (F0.map (ptsArr AB treeF.1 treeF.2 3850))

@[expose] def orbSet : Std.HashSet (List Bool) := Std.HashSet.ofList orbF

@[expose] def treeOK : Bool :=
  enumOK 3850 AB treeF.1 treeF.2 && decide orbF.Nodup

@[expose] def quickOK (y yi e : Array Nat) : Bool :=
  (List.range 100).any (fun q => img y (img e (img yi q)) != img e q) &&
    (List.range 100).all fun q =>
      img e (img y (img e (img yi q))) == img y (img e (img yi (img e q)))

@[expose] def loopOK : Bool :=
  s5Elems.toList.all fun y =>
    y == idT 100 ||
      (let yi := invT y
       invList.all fun e =>
         !(quickOK y yi e) ||
           (let es := conj5 y yi e
            !(pwComm es) || (pwDistinct (subsetProds (es.take 4)) && orbSet.contains (maskOf (fixPts es)))))

@[expose] def mPres : Bool :=
  mTabs.all fun t =>
    F0.all (fun f => F0.contains (img t f)) &&
      ((img t 0 == 0 && img t 1 == 1) || (img t 0 == 1 && img t 1 == 0))

@[expose] def kCount : Bool :=
  decide ((mElems.toList.filter fun t => img t 0 == 0 && img t 1 == 1).length ≤ 5760)

@[expose] def kInM : Bool :=
  kTabs.all fun t => img t 0 == 0 && img t 1 == 1 && mElems.toList.contains t

@[expose] def uTab : Array Nat := hs100Arr 15

@[expose] def kU : Nat := 1619

@[expose] def kUOK : Bool :=
  orbF.getD kU [] == maskOf (F0.map (img (invT uTab)))

@[expose] def treeElems : Array (Array Nat) := enumTabs AB treeF 3850

@[expose] def wTab : Array Nat := compT uTab (treeElems.getD kU #[])

@[expose] def centOK : Bool :=
  mElems.toList.all fun m => !(commT m (kTabs.getD 0 #[]) && commT m (kTabs.getD 1 #[])) || m == idT 100

@[expose] def centWOK : Bool :=
  mElems.toList.all fun m =>
    let wm := compT wTab m
    !(commT wm (kTabs.getD 0 #[]) && commT wm (kTabs.getD 1 #[]))

end CFSG.Quasithin.H13.LocDbl.HSLoc
