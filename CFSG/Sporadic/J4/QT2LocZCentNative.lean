module

public import CFSG.Sporadic.J4.QT2LocX0Native
public import CFSG.Sporadic.J4.QTRankNative
public import Std.Data.HashSet.Basic

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def zcGenWords : List (List Int) :=
  [[-1, -2, -1, -2, -3, 1, 3, -2], [-1, -1, -2, -3, -3, -2, 3, 2],
    [-1, -2, 1, 3, 1, -2, 3, 3, 1]]

@[expose] def zcGenTabs : List (List Nat) := zcGenWords.map wordT

@[expose] def zcFast (g : List Nat) : Array Nat × Array Nat :=
  ((Array.range 64).map fun c => actT g c, (Array.range 32).map fun c => actT g (c <<< 6))

@[inline, expose] def zcAct (f : Array Nat × Array Nat) (c : Nat) : Nat :=
  f.1[c &&& 63]! ^^^ f.2[c >>> 6]!

@[expose] def zcStep (f : Array Nat × Array Nat) (t : Array Nat) : Array Nat :=
  t.map (zcAct f)

@[expose] def zcKey (t : Array Nat) : Nat := t.foldl (fun acc x => acc * 2048 + x) 0

@[expose] def zcId : Array Nat := (List.range 11).toArray.map fun j => 2 ^ j

@[expose] def zcEnum (fs : Array (Array Nat × Array Nat)) (cap : Nat) :
    Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut tabs : Array (Array Nat) := #[zcId]
  let mut par : Array Nat := #[0]
  let mut gi : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert (zcKey zcId)
  let mut q := 0
  for _ in [0:cap] do
    if q < tabs.size then
      let t := tabs[q]!
      for g in [0:fs.size] do
        let u := zcStep fs[g]! t
        let k := zcKey u
        if !seen.contains k then
          seen := seen.insert k
          tabs := tabs.push u
          par := par.push q
          gi := gi.push g
      q := q + 1
  return (tabs, par, gi)

@[expose] def zcFasts : Array (Array Nat × Array Nat) := (zcGenTabs.map zcFast).toArray

@[expose] def zcData : Array (Array Nat) × Array Nat × Array Nat := zcEnum zcFasts 1000000

@[expose] def zcN : Nat := 887040

@[expose] def zcTab (j : Nat) : List Nat := (zcData.1[j]!).toList

@[expose] def zcPar (j : Nat) : Nat := zcData.2.1[j]!

@[expose] def zcGi (j : Nat) : Nat := zcData.2.2[j]!

@[expose] def zcWordAux : Nat → Nat → List Int
  | 0, _ => []
  | f + 1, j => if j == 0 then [] else (zcGenWords.getD (zcGi j) []) ++ zcWordAux f (zcPar j)

@[expose] def zcDepth : Nat := 300

@[expose] def zcWord (j : Nat) : List Int := zcWordAux zcDepth j

@[expose] def zcEntryOK (t : Array Nat) : Bool := t.size == 11 && t.all (· < 2048)

@[expose] def zcDepths : Array Nat := Id.run do
  let mut d : Array Nat := Array.mkEmpty zcN
  for j in [0:zcN] do
    d := d.push (if j == 0 then 0 else d[zcPar j]! + 1)
  return d

@[expose] def zcTreeOK : Bool :=
  zcData.1.size == zcN && zcData.2.1.size == zcN && zcData.2.2.size == zcN &&
    zcData.1[0]! == zcId &&
    (List.range zcN).all fun j =>
      zcEntryOK zcData.1[j]! &&
        (j == 0 || (zcPar j < j && zcGi j < 3 &&
          zcData.1[j]! == zcStep (zcFasts[zcGi j]!) (zcData.1[zcPar j]!)))

@[expose] def zcDepthOK : Bool :=
  zcDepths.size == zcN && (List.range zcN).all fun j =>
    zcDepths[j]! ≤ zcDepth && zcDepths[j]! == (if j == 0 then 0 else zcDepths[zcPar j]! + 1)

@[expose] def strictInc : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a < b) && strictInc (b :: l)

@[expose] def zcDistinctOK : Bool :=
  strictInc ((zcData.1.toList.map zcKey).mergeSort (· ≤ ·))

@[expose] def zcGenOK : Bool :=
  zcGenTabs.length == 3 &&
    zcGenTabs.all (fun g => g.length == 11 && g.all (· < 2048) && actT g 1 == 1) &&
    zcGenTabs.all fun g =>
      (List.range 2048).all fun c => zcAct (zcFast g) c == actT g c

@[expose] def zcLocWf : Bool :=
  (locMats ()).size == 3 && (locInvs ()).size == 3 && (locMats ()).all wfRows &&
    (locInvs ()).all wfRows

@[expose] def zcOK : Bool := zcLocWf && zcGenOK && zcTreeOK && zcDepthOK && zcDistinctOK

@[expose] def actA (t : Array Nat) (c : Nat) : Nat :=
  (List.range 11).foldl (fun acc k => if c.testBit k then acc ^^^ t[k]! else acc) 0

@[expose] def commA (t u : Array Nat) : Bool :=
  (List.range 11).all fun k => actA t (u[k]!) == actA u (t[k]!)

@[expose] def zcTaus (Ts : List (List Nat)) : List Nat :=
  (List.range zcN).filter fun j => Ts.all fun T => commA (zcData.1[j]!) T.toArray

end CFSG.Sporadic.J4.QT2
