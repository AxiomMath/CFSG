module

public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

set_option compiler.extract_closed false

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def fixOctIdTab : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] def mulTab (a b : Array Nat) : Array Nat := (Array.range 24).map fun i => a[b[i]!]!

@[expose] def invTab (a : Array Nat) : Array Nat :=
  (Array.range 24).map fun v => ((List.range 24).find? fun i => a[i]! == v).getD 0

@[expose] def commTab (a b : Array Nat) : Array Nat :=
  mulTab a (mulTab b (mulTab (invTab a) (invTab b)))

@[expose] def tabKey (t : Array Nat) : Nat := t.foldl (fun acc m => (acc <<< 8) ||| m) 0

@[expose] def fixOctA1 : Array Nat :=
  #[4, 3, 1, 6, 0, 7, 5, 2, 15, 8, 10, 13, 11, 12, 14, 9, 21, 18, 16, 23, 17, 22, 20, 19]

@[expose] def fixOctB1 : Array Nat :=
  #[3, 1, 2, 0, 5, 7, 4, 6, 14, 12, 15, 13, 8, 10, 9, 11, 16, 18, 17, 19, 22, 20, 23, 21]

@[expose] def fixOctA2 : Array Nat :=
  #[6, 0, 7, 1, 2, 4, 3, 5, 10, 12, 11, 13, 14, 8, 15, 9, 21, 19, 20, 18, 17, 23, 16, 22]

@[expose] def fixOctB2 : Array Nat :=
  #[7, 6, 4, 5, 2, 3, 1, 0, 13, 12, 14, 15, 8, 9, 11, 10, 21, 20, 22, 23, 16, 17, 19, 18]

@[expose] def fixOctComm1 : Array Nat :=
  #[3, 1, 5, 7, 4, 6, 2, 0, 10, 8, 12, 14, 13, 15, 11, 9, 18, 16, 20, 22, 21, 23, 19, 17]

@[expose] def fixOctComm2 : Array Nat :=
  #[2, 5, 1, 6, 7, 0, 4, 3, 14, 9, 13, 10, 11, 12, 8, 15, 16, 23, 19, 20, 21, 18, 22, 17]

@[expose] def fixOctComms (_ : Unit := ()) : List (Array Nat) := [fixOctComm1, fixOctComm2]

@[expose] def fixOctCommCheck (_ : Unit := ()) : Bool :=
  (commTab fixOctA1 fixOctB1 == fixOctComm1) && (commTab fixOctA2 fixOctB2 == fixOctComm2)

@[expose] def fixOctSteps (_ : Unit := ()) : List (Array Nat → Array Nat) :=
  (fixOctComms ()).map fun g => fun t => mulTab g t

@[expose] def fixOctClosure (_ : Unit := ()) : Array (Array Nat) × Array Nat × Array Nat :=
  bfs tabKey (fixOctSteps ()) fixOctIdTab 11000

@[expose] def closureSizeOK (r : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  decide (10752 ≤ r.1.size)

@[expose] def closureNodupOK (r : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  decide r.1.toList.Nodup

@[expose] def closureBaseOK (r : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  r.1[0]! == fixOctIdTab

@[expose] def closureTreeOK (gs : List (Array Nat))
    (r : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  allLt r.1.size (fun p => p == 0 ||
    ((decide (r.2.1[p]! < p)) && ((decide (r.2.2[p]! < 2)) &&
      (mulTab (gs.getD r.2.2[p]! #[]) r.1[r.2.1[p]!]! == r.1[p]!))))

@[expose] def closureWidthOK (r : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  allLt r.1.size (fun p => (r.1[p]!).size == 24)

@[expose] def fixOctPerfectCheckParts (_ : Unit := ()) : List Bool :=
  let r := fixOctClosure ()
  let gs := fixOctComms ()
  [fixOctCommCheck (), closureSizeOK r, closureBaseOK r, closureNodupOK r, closureTreeOK gs r,
    closureWidthOK r]

@[expose] def fixOctPerfectCheck (_ : Unit := ()) : Bool :=
  (fixOctPerfectCheckParts ()).all id

end CFSG.Quasithin.H13.AS91.M24G.Native
