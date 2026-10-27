module

public import Certificates.Data.CFSGNative.AS91.M24Syl

public section

set_option compiler.extract_closed false

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def duadMask (i j : Nat) : Nat := actM ccEColsN ((1 <<< i) ||| (1 <<< j))

@[expose] def duadMasks (_ : Unit := ()) : List Nat :=
  (List.range 24).flatMap fun i => ((List.range 24).filter fun j => i < j).map fun j =>
    duadMask i j

@[expose] def duadCoverCheck (_ : Unit := ()) : Bool :=
  let dm := duadMasks ()
  let sc := scTab (clsTab (sextList ()))
  allLt 2048 fun m => m == 0 || dm.contains m || sc[m]!

@[expose] def duadT0 (_ : Unit := ()) : Nat := duadMask 0 1

@[expose] def duadF770 (_ : Unit := ()) : Nat :=
  actM ccEColsN (1 ||| (1 <<< 3) ||| (1 <<< 4) ||| (1 <<< 5))

@[expose] def duadPpGens : List (Array Nat) :=
  [#[0, 1, 7, 16, 5, 9, 19, 10, 8, 13, 21, 3, 4, 12, 14, 18, 15, 2, 11, 20, 23, 17, 6, 22],
    #[1, 0, 7, 13, 23, 14, 5, 20, 22, 9, 2, 18, 10, 12, 11, 6, 19, 15, 17, 4, 21, 16, 3, 8]]

@[expose] def duadPairKey (t₀ m : Nat) : Nat := min m (m ^^^ t₀)

@[expose] def duadPairOrbitCheck (_ : Unit := ()) : Bool :=
  let t0 := duadT0 ()
  let f := duadF770 ()
  let steps := duadPpGens.map fun g m => toddAct g m
  let r := bfs (duadPairKey t0) steps f 900
  treeValid (fun m => decide (m < 2048)) steps f r && decide (770 ≤ r.1.size) &&
    decide (r.1.toList.map (duadPairKey t0)).Nodup

@[expose] def duadComp (a b : Array Nat) : Array Nat := (Array.range 24).map fun i => a[b[i]!]!

@[expose] def duadId (_ : Unit := ()) : Array Nat := Array.range 24

@[expose] def duadKey (t : Array Nat) : Nat := t.foldl (fun acc x => acc * 24 + x) 0

@[expose] def duadValidTab (t : Array Nat) : Bool := t.size == 24

@[expose] def duadGrpData (gens : List (Array Nat)) (n : Nat) :
    Array (Array Nat) × Array Nat × Array Nat :=
  bfs duadKey (gens.map fun g t => duadComp g t) (duadId ()) (n + 5)

@[expose] def duadGrpCheck (gens : List (Array Nat)) (n : Nat) : Bool :=
  let steps := gens.map fun g t => duadComp g t
  let idt := duadId ()
  let r := duadGrpData gens n
  let L := r.1
  treeValid duadValidTab steps idt r && L.size == n && decide L.toList.Nodup &&
    gens.all (fun g => L.contains g) &&
    allLt n (fun i => allLt n fun j => L.contains (duadComp L[i]! L[j]!)) &&
    allLt n fun i => L.any fun t => duadComp L[i]! t == idt

@[expose] def duadInvs (L : Array (Array Nat)) (n : Nat) : List Nat :=
  let idt := duadId ()
  (List.range n).filter fun i => duadComp L[i]! L[i]! == idt

@[expose] def duadCommWith (L : Array (Array Nat)) (invs : List Nat) (i : Nat) : List Nat :=
  invs.filter fun j => duadComp L[i]! L[j]! == duadComp L[j]! L[i]!

@[expose] def duadBad (L : Array (Array Nat)) (n : Nat) : List Nat :=
  let invs := duadInvs L n
  invs.filter fun i => 32 ≤ (duadCommWith L invs i).length

@[expose] def duadEaCheck (gens : List (Array Nat)) (n : Nat) : Bool :=
  decide ((duadBad (duadGrpData gens n).1 n).length < 32)

@[expose] def duadP1Gens : List (Array Nat) :=
  [#[0, 1, 2, 3, 4, 5, 6, 7, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20],
    #[0, 1, 2, 3, 18, 19, 16, 17, 12, 15, 13, 14, 11, 9, 8, 10, 7, 6, 5, 4, 21, 20, 23, 22],
    #[1, 0, 2, 3, 4, 6, 5, 7, 8, 11, 10, 9, 19, 16, 17, 18, 13, 14, 15, 12, 22, 21, 20, 23]]

@[expose] def duadP2Gens : List (Array Nat) :=
  [#[0, 1, 2, 3, 4, 5, 6, 7, 18, 19, 16, 17, 22, 23, 20, 21, 10, 11, 8, 9, 14, 15, 12, 13],
    #[1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10, 13, 12, 14, 15, 22, 23, 21, 20, 19, 18, 16, 17],
    #[1, 0, 3, 2, 7, 6, 5, 4, 8, 9, 10, 11, 14, 15, 12, 13, 18, 19, 16, 17, 20, 21, 22, 23]]

@[expose] def duadQ3Gens : List (Array Nat) :=
  [#[0, 1, 2, 4, 5, 3, 6, 7, 8, 15, 18, 21, 19, 20, 9, 14, 10, 13, 16, 23, 17, 22, 11, 12],
    #[0, 1, 6, 4, 5, 3, 7, 2, 8, 19, 16, 11, 20, 15, 12, 23, 18, 9, 10, 17, 14, 21, 22, 13]]

@[expose] def duadS2Check (_ : Unit := ()) : Bool :=
  let t0 := duadT0 ()
  let f := duadF770 ()
  (duadP2Gens ++ duadQ3Gens).all fun g => toddAct g f == f || toddAct g f == f ^^^ t0

@[expose] def duadX1120 (_ : Unit := ()) : Nat :=
  actM ccEColsN (1 ||| (1 <<< 3) ||| (1 <<< 4) ||| (1 <<< 8))

@[expose] def duadXWit : List (Array Nat) :=
  [#[0, 1, 2, 17, 14, 21, 10, 7, 23, 15, 5, 9, 19, 16, 3, 18, 22, 4, 11, 12, 13, 6, 20, 8],
    #[0, 1, 2, 13, 22, 18, 9, 7, 19, 5, 11, 21, 23, 4, 16, 10, 17, 20, 6, 8, 14, 15, 3, 12],
    #[0, 1, 2, 20, 16, 15, 11, 7, 12, 10, 18, 5, 8, 17, 13, 6, 3, 22, 21, 23, 4, 9, 14, 19]]

@[expose] def duadSatCheck (_ : Unit := ()) : Bool :=
  let x := duadX1120 ()
  let t0 := duadT0 ()
  let t02 := duadMask 0 2
  duadXWit.length == 3 && toddAct (duadXWit.getD 0 #[]) x == x ^^^ t0 &&
    toddAct (duadXWit.getD 1 #[]) x == x ^^^ t02 &&
    toddAct (duadXWit.getD 2 #[]) x == x ^^^ (t0 ^^^ t02)

@[expose] def duadCheck (_ : Unit := ()) : Bool :=
  duadCoverCheck () && duadPairOrbitCheck () && duadGrpCheck duadP1Gens 128 &&
    duadEaCheck duadP1Gens 128 && duadGrpCheck duadP2Gens 128 && duadEaCheck duadP2Gens 128 &&
    duadGrpCheck duadQ3Gens 9 && duadS2Check () && duadSatCheck ()

end CFSG.Quasithin.H13.AS91.M24G.Native
