module

public import CFSG.Sporadic.J4.QT2LocHNative
public import CFSG.Sporadic.J4.QT2LocX0Native

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def vlSeedIdx (s : List Nat) : Nat :=
  ((List.range 1024).find? fun e => seqT (pcSeq e) == s).getD 0

@[expose] def vlKelWord (e : Nat) : List Int := (pcSeq e).flatMap fun i => kWords.getD i []

@[expose] def vlTree (seeds : List (List Nat)) (fuel : Nat) : Array (List Nat × Nat × Int) :=
  Id.run do
    let mut seen : Std.HashSet (List Nat) := {}
    let mut arr : Array (List Nat × Nat × Int) := #[]
    for s in seeds do
      if !seen.contains s then
        seen := seen.insert s
        arr := arr.push (s, 0, 0)
    let mut i := 0
    for _ in [0:fuel] do
      if i < arr.size then
        let t := arr[i]!.1
        for ℓ in letters do
          let u := letConj ℓ t
          if !seen.contains u then
            seen := seen.insert u
            arr := arr.push (u, i, ℓ)
        i := i + 1
    return arr

@[expose] def vlInvTree : Array (List Nat × Nat × Int) := vlTree invSeedsT 60000

@[expose] def vlNodeMap : Std.HashMap (List Nat) Nat := Id.run do
  let mut m : Std.HashMap (List Nat) Nat := {}
  for i in [0:vlInvTree.size] do
    let t := (vlInvTree[i]!).1
    if !m.contains t then m := m.insert t i
  return m

@[expose] def vlNodeOf (y : List Nat) : Nat := (vlNodeMap.get? y).getD 0

@[expose] def vlLiftAux (tr : Array (List Nat × Nat × Int)) : Nat → Nat → List Int
  | 0, _ => []
  | f + 1, i =>
    let r := tr[i]!
    if r.2.2 == 0 then vlKelWord (vlSeedIdx r.1)
    else r.2.2 :: (vlLiftAux tr f r.2.1 ++ [-r.2.2])

@[expose] def vlLiftWord (y : List Nat) : List Int := vlLiftAux vlInvTree 200 (vlNodeOf y)

@[expose] def vlTables : List (List Nat) := vGroups.flatten.filter (· != idT)

@[expose] def vlLiftTab : Array (Array V2) := (vlTables.map fun y => wR (vlLiftWord y)).toArray

@[expose] def vlTabIdx (y : List Nat) : Nat := (vlTables.findIdx? (· == y)).getD 0

@[expose] def vlLiftRows (y : List Nat) : Array V2 := vlLiftTab[vlTabIdx y]!

@[expose] def chkVlLifts : Bool :=
  vlTables.length == 75 && vlTables.all fun y =>
    (vlLiftWord y).all (fun l => letters.contains l) && wordT (vlLiftWord y) == y

@[expose] def chkVlLiftWf : Bool :=
  vlTables.all fun y => wfRows (vlLiftRows y) && eqRows (vlLiftRows y) (wR (vlLiftWord y))

@[expose] def vlEtaTab : Array (Array V2) :=
  let T := uTab (locMats ()) (locInvs ())
  (Array.range 2048).map fun c => etaRows T 11 c

@[expose] def chkVlEta : Bool := vlEtaTab.size == 2048 && vlEtaTab.all wfRows && wfRows idRows

@[expose] def vlXiConj (t : Array V2) : Array V2 :=
  mulRows (mulRows (x0GenRows[0]!) t) (x0InvRows[0]!)

@[expose] def vlComm (a b : Array V2) : Bool := eqRows (mulRows a b) (mulRows b a)

@[expose] def vlValid (t : Array V2) : Bool :=
  eqRows (mulRows t t) idRows &&
    (let t1 := vlXiConj t
     let t2 := vlXiConj t1
     vlComm t t1 && vlComm t t2 &&
       (let t3 := vlXiConj t2
        let t4 := vlXiConj t3
        eqRows (mulRows (mulRows (mulRows (mulRows t t1) t2) t3) t4) idRows))

@[expose] def vlT (p : List Nat × Nat) : Array V2 := mulRows vlEtaTab[p.2]! (vlLiftRows p.1)

@[expose] def vlPairs : List (List Nat × Nat) :=
  vlTables.flatMap fun y =>
    let S := vlLiftRows y
    (List.range 2048).filterMap fun e =>
      if vlValid (mulRows vlEtaTab[e]! S) then some (y, e) else none

@[expose] def vlConjs (t : Array V2) : Array (Array V2) :=
  let t1 := vlXiConj t
  let t2 := vlXiConj t1
  #[t, t1, t2, vlXiConj t2]

@[expose] def vlSubsetProd (ts : Array (Array V2)) (m : Nat) : Array V2 :=
  (List.range 4).foldl (fun acc i => if m.testBit i then mulRows acc ts[i]! else acc) idRows

@[expose] def vlGroupOf (t : Array V2) : List (Array V2) :=
  let ts := vlConjs t
  (List.range 16).map (vlSubsetProd ts)

@[expose] def vlDistinct (G : List (Array V2)) : Bool :=
  G.length == 16 && (List.range 16).all fun i => (List.range i).all fun j =>
    !eqRows (G.getD i #[]) (G.getD j #[])

@[expose] def vlGroups : List (List (Array V2)) :=
  vlPairs.foldl (fun acc p =>
    let t := vlT p
    if acc.any (fun G => G.any (eqRows t)) then acc else acc ++ [vlGroupOf t]) []

@[expose] def chkVlGroups : Bool :=
  vlPairs.length == 1980 && vlGroups.length == 132 &&
    vlPairs.all fun p =>
      let Gt := vlGroupOf (vlT p)
      vlDistinct Gt && vlGroups.any fun G => Gt.all fun M => G.any (eqRows M)

@[expose] def chkVlLines : Bool := lines17.length == 17

@[expose] def chkVlAll : Bool :=
  chkVlLifts && chkVlLiftWf && chkVlEta && chkVlGroups && chkVlLines

end CFSG.Sporadic.J4.QT2
