module

public import CFSG.Sporadic.J4.QT2LocVLNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B336Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Words

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def vlAll : Array (Array (Array V2)) :=
  ((lines17.map fun S => (S.map etaE).toArray) ++ vlGroups.map List.toArray).toArray

@[expose] def vlCx : Array (Array V2) := x0Orb.mats

@[expose] def vlCxInv : Array (Array V2) := vlCx.map invRows

@[expose] def vlConjBy (c : Nat) (M : Array V2) : Array V2 :=
  mulRows (mulRows vlCx[c]! M) vlCxInv[c]!

@[expose] def vlIdxMap : Std.HashMap UInt64 (List Nat) := Id.run do
  let mut m : Std.HashMap UInt64 (List Nat) := {}
  for g in [0:vlAll.size] do
    for i in [1:16] do
      let h := rowsHash (vlAll[g]!.getD i #[])
      m := m.insert h (g :: (m.getD h []))
  return m

@[expose] def vlFind (X : Array V2) : Option Nat :=
  ((vlIdxMap.getD (rowsHash X) []).reverse.filter fun g =>
    (List.range 15).any fun i => eqRows X (vlAll[g]!.getD (i + 1) #[])).head?

@[expose] def vlOrbitOf (r : Nat) : List (Nat × Nat) := Id.run do
  let t := vlAll[r]!.getD 1 #[]
  let mut res : Array (Nat × Nat) := #[]
  let mut seen : Std.HashSet Nat := {}
  for c in [0:vlCx.size] do
    match vlFind (vlConjBy c t) with
    | none => pure ()
    | some g =>
      if !seen.contains g then
        seen := seen.insert g
        res := res.push (g, c)
  return res.toList

@[expose] def vlW5 (s : String) : List Int :=
  s.toList.filterMap fun ch =>
    if 'a' ≤ ch ∧ ch ≤ 'e' then some ((ch.toNat - 'a'.toNat + 1 : Nat) : Int)
    else if 'A' ≤ ch ∧ ch ≤ 'E' then some (-((ch.toNat - 'A'.toNat + 1 : Nat) : Int))
    else none

@[expose] def vlA941Strs : List String := [
    ("cABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACaaABAbaabAABAbaabAABAbaabA" ++
      "ABAbaabAABAbaabAABAbaabAABAbaabAAAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabA" ++
      "ABAbaabABBacABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABA" ++
      "baabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAABCbCCBACbaBCaCaACCbABaabcccaC"),
    ("aABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAcABAbaabAABAbaabAABAbaabAA" ++
      "BAbaabAABAbaabAABAbaabAABAbaabACbaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
      "AbaabAABcaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAACbaaABAbaabAABAba" ++
      "abAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAABAAAAbbccBCBcAbBAbCaaacBABAAc"),
    ("aABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAbABAbaabAABAbaabAABAbaabAA" ++
      "BAbaabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABA" ++
      "baabACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAcaABAbaabAABAbaabA" ++
      "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAACabABAbaabAABAbaabAABAbaabAABAbaabAABAbaabA" ++
      "ABAbaabAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBbaaABA" ++
      "baabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAABaccAbccbACbabaAAbACbbAccabAc"),
    ("ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAacABAbaabAABAbaabAABAbaabAAB" ++
      "AbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAA" ++
      "BAbaabAAABcABBAbcACABBcABaBaCAbbaCCBaa")]

@[expose] def vlA21Masks : List Nat := [1056, 321, 43, 796]

@[expose] def vlA77Masks : List Nat := [768, 299, 213, 1414]

@[expose] def vlB56Masks : List Nat := [25, 136, 833, 1312]

@[expose] def vlB336Word : List Int :=
  vlW5 "cAAccAccABCccBBCccBBCccBBCccBBCccBccAccAAbcBAbcBAbcBAbcBAbcBAbcBAbcBaaC"

@[expose] def gsMasks (cs : List Nat) : Array (Array V2) := (cs.map etaE).toArray

@[expose] def gsWords (ws : List (List Int)) : Array (Array V2) := (ws.map wR).toArray

@[expose] def gsXi (e : Nat) : Array (Array V2) :=
  vlConjs (mulRows (etaE e) (wR vlB336Word))

@[expose] def vlNamedGs : List (Array (Array V2)) :=
  [gsMasks vlA21Masks, gsMasks vlA77Masks, gsWords (vlA941Strs.map vlW5),
    gsWords CFSG.QuasithinUnique.A5.B7.b7ExplicitWords,
    gsWords CFSG.QuasithinUnique.A5.Dec2.wsB336, gsMasks vlB56Masks, gsXi 37, gsXi 97, gsXi 236,
    gsXi 491]

@[expose] def vlSameSet (gs : Array (Array V2)) (B : Array (Array V2)) : Bool :=
  let A := (List.range 16).map (vlSubsetProd gs)
  A.all (fun M => B.any (eqRows M)) && B.all (fun M => A.any (eqRows M))

@[expose] def vlIdxOf (gs : Array (Array V2)) : Nat :=
  ((List.range vlAll.size).find? fun g => vlSameSet gs vlAll[g]!).getD 1000

@[expose] def vlPref : List Nat := (vlNamedGs.take 5).map vlIdxOf

@[expose] def vlRepIdx : List Nat := vlPref ++ [1, 21, 22, 24, 28]


@[expose] def vlClasses : List (Nat × (Nat × Nat)) := Id.run do
  let mut wit : Array (Option (Nat × Nat)) := Array.replicate vlAll.size none
  let mut out : Array (Nat × (Nat × Nat)) := #[]
  for g in vlPref ++ List.range vlAll.size do
    if (wit[g]!).isNone then
      for (g', c) in vlOrbitOf g do
        if (wit[g']!).isNone then
          wit := wit.set! g' (some (g, c))
          out := out.push (g', (g, c))
  return out.toList

@[expose] def vlConjEq (r g c : Nat) : Bool :=
  let cs := vlAll[r]!.map (vlConjBy c)
  (cs.all fun X => vlAll[g]!.any (eqRows X)) &&
    (vlAll[g]!.all fun M' => cs.any fun X => eqRows X M')

@[expose] def vlNumClasses : Nat := (vlClasses.filter fun x => x.1 == x.2.1).length

@[expose] def chkVlClass : Bool :=
  vlCx.size == 6720 && vlAll.size == 149 && vlAll.all (·.size == 16) &&
    (List.range 6720).all (fun c => wfRows vlCx[c]! && wfRows vlCxInv[c]! &&
      eqRows (mulRows vlCx[c]! vlCxInv[c]!) idRows &&
      eqRows (mulRows vlCxInv[c]! vlCx[c]!) idRows) &&
    vlClasses.length == 149 &&
    (List.range 149).all (fun g => vlClasses.any fun x => x.1 == g && decide (x.2.2 < 6720)) &&
    vlClasses.all (fun x => vlConjEq x.2.1 x.1 x.2.2 && vlRepIdx.contains x.2.1) &&
    vlNumClasses == vlRepIdx.length

@[expose] def vrClosedB (A : Array (Array V2)) : Bool :=
  A.any (eqRows idRows) &&
    A.all fun M => eqRows (mulRows M M) idRows &&
      A.all fun N => A.any fun K => eqRows (mulRows M N) K

@[expose] def chkNamed : Bool :=
  vlNamedGs.map vlIdxOf == vlRepIdx &&
    (List.zip vlRepIdx vlNamedGs).all fun x =>
      let A := vlAll[x.1]!
      vrClosedB A && A.size == 16 &&
        (List.range 4).all (fun i => wfRows (x.2[i]!) && A.any (eqRows (x.2[i]!))) &&
        (List.range 16).all (fun m => A.any (eqRows (vlSubsetProd x.2 m))) &&
        (List.range 16).all fun m => (List.range 16).all fun m' =>
          !(eqRows (vlSubsetProd x.2 m) (vlSubsetProd x.2 m')) || m == m'

@[expose] def chkVlAll2 : Bool := chkVlClass && chkNamed

end CFSG.Sporadic.J4.QT2
