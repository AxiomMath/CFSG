module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Check

public section

namespace CFSG.KC.EvenSporP12

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

@[expose] def encL : List Nat → Nat
  | [] => 0
  | x :: xs => x + 16 * encL xs

@[expose] def enc (a : Array Nat) : Nat := encL a.toList

@[expose] def dig (P i : Nat) : Nat := P / 16 ^ i % 16

@[expose] def pidK (n : Nat) : Nat := encL (List.range n)

@[expose] def pmulK (n P Q : Nat) : Nat := encL ((List.range n).map fun i => dig P (dig Q i))

@[expose] def commK (n P Q : Nat) : Bool :=
  (List.range n).all fun i => dig P (dig Q i) == dig Q (dig P i)

@[expose] def sqK (n P : Nat) : Bool := (List.range n).all fun i => dig P (dig P i) == i

@[expose] def wordK (n : Nat) (G : List Nat) (w : List Nat) : Nat :=
  w.foldr (fun l acc => pmulK n (G.getD l 0) acc) (pidK n)

@[expose] def stepK (n : Nat) (G : List Nat) (x : Nat) (w : List Nat)
    (acc : List (Nat × List Nat)) (k : Nat) : List (Nat × List Nat) :=
  let y := pmulK n x (G.getD k 0)
  if acc.any (fun e => e.1 == y) then acc else acc ++ [(y, w ++ [k])]

@[expose] def goK (n : Nat) (G : List Nat) : Nat → Nat → List (Nat × List Nat) →
    List (Nat × List Nat)
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
    if i < acc.length then
      goK n G fuel (i + 1) ((List.range G.length).foldl
        (stepK n G (acc.getD i (0, [])).1 (acc.getD i (0, [])).2) acc)
    else acc

@[expose] def wordsOfK (n : Nat) (G : List Nat) : List (List Nat) :=
  (goK n G 2000 0 [(pidK n, [])]).map (·.2)

@[expose] def allDistinctK : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && allDistinctK xs

@[expose] def enumOKK (n : Nat) (G : List Nat) (L : List (List Nat)) : Bool :=
  let vals := L.map (wordK n G)
  L.all (fun w => w.all (· < G.length)) && L.contains [] &&
    (List.range G.length).all
      (fun k => vals.all fun v => vals.contains (pmulK n v (G.getD k 0))) &&
    allDistinctK vals

@[expose] def elemAbOKK (n : Nat) (EG : List Nat) : Bool :=
  EG.all (sqK n) && EG.all fun x => EG.all fun y => commK n x y

@[expose] def tripleK (n : Nat) (Cx : List Nat) : List Nat :=
  Cx.filter fun y => sqK n y && 64 ≤ (Cx.filter (commK n y)).length

@[expose] def countAtK (n : Nat) (PV : List Nat) (x : Nat) : Bool :=
  (tripleK n (PV.filter (commK n x))).length < 64

@[expose] def countOKK (n : Nat) (PV EV : List Nat) : Bool :=
  PV.all fun x => x == pidK n || !sqK n x || EV.contains x || countAtK n PV x

@[expose] def order8OKK (n : Nat) (G : List Nat) (w : List Nat) : Bool :=
  let g := wordK n G w
  let g2 := pmulK n g g
  let g4 := pmulK n g2 g2
  let g8 := pmulK n g4 g4
  w.all (· < G.length) && g4 != pidK n && g8 == pidK n

@[expose] def normOKK (n : Nat) (EV EG : List Nat) (c : Nat) : Bool :=
  pmulK n c (pmulK n c c) == pidK n &&
    EG.all fun u => EV.contains (pmulK n (pmulK n c u) (pmulK n c c))

@[expose] def p12CheckK (n : Nat) : Bool :=
  let PG := (pGenSw.map (swapsArr n)).map enc
  let EG := (eGenSw.map (swapsArr n)).map enc
  let CG := (cGenSw.map (swapsArr n)).map enc
  let PW := wordsOfK n PG
  let EW := wordsOfK n EG
  let CW := wordsOfK n CG
  let PV := PW.map (wordK n PG)
  let EV := EW.map (wordK n EG)
  pGenSw.all (swapsOK n) && eGenSw.all (swapsOK n) && cGenSw.all (swapsOK n) &&
    enumOKK n PG PW && PW.length == 512 && enumOKK n EG EW && EW.length == 64 &&
    enumOKK n CG CW && CW.length == 9 && elemAbOKK n EG && EG.all (PV.contains ·) &&
    order8OKK n PG gWord && countOKK n PV EV && CG.all (normOKK n EV EG)

end CFSG.KC.EvenSporP12
