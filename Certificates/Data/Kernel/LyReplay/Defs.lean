module

public import CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs

public section

namespace CFSG.KC.LyReplay

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] def letterOfCode (n : Nat) : Fin 6 × Bool :=
  match n % 12 with
  | 0 => (0, true) | 1 => (0, false) | 2 => (1, true) | 3 => (1, false)
  | 4 => (2, true) | 5 => (2, false) | 6 => (3, true) | 7 => (3, false)
  | 8 => (4, true) | 9 => (4, false) | 10 => (5, true) | _ => (5, false)

@[expose] def charOfCode (n : Nat) : Char :=
  match n % 12 with
  | 0 => 'c' | 1 => 'C' | 2 => 'd' | 3 => 'D'
  | 4 => 'a' | 5 => 'A' | 6 => 'b' | 7 => 'B'
  | 8 => 'e' | 9 => 'E' | 10 => 'k' | _ => 'K'

@[expose] def wordOf (w : List Nat) : List (Fin 6 × Bool) := w.map letterOfCode

@[expose] def strOf (w : List Nat) : String := String.ofList (w.map charOfCode)

@[expose] def kindOf : Nat → Dist2Kind
  | 0 => .B
  | 1 => .K
  | 2 => .E
  | _ => .T

@[expose] def stepOf (s : Nat × Nat × List Nat × List Nat) : Dist2Step :=
  ⟨s.1, kindOf s.2.1, strOf s.2.2.1, strOf s.2.2.2⟩

@[expose] def derivOf (st : List Nat) (ss : List (Nat × Nat × List Nat × List Nat)) : Dist2Deriv :=
  ⟨strOf st, ss.map stepOf⟩

@[expose] def rulesOf (R : List (List Nat × List Nat)) :
    List (List (Fin 6 × Bool) × List (Fin 6 × Bool)) :=
  R.map fun r => (wordOf r.1, wordOf r.2)

@[expose] def stepOKW (kR eR tR : List (List (Fin 6 × Bool) × List (Fin 6 × Bool)))
    (k : Dist2Kind) (old new : List (Fin 6 × Bool)) : Bool :=
  match k with
  | .B => true
  | .K => ruleOK kR old new
  | .E => ruleOK eR old new
  | .T => ruleOK tR old new

@[expose] def replayW (kR eR tR : List (List (Fin 6 × Bool) × List (Fin 6 × Bool))) :
    List (Fin 6 × Bool) → List (Nat × Nat × List Nat × List Nat) → Bool
  | cur, [] => cur.isEmpty
  | cur, s :: ss =>
    stepOKW kR eR tR (kindOf s.2.1) (wordOf s.2.2.1) (wordOf s.2.2.2) &&
      match replaceAt cur s.1 (wordOf s.2.2.1) (wordOf s.2.2.2) with
      | some cur' => replayW kR eR tR cur' ss
      | none => false

end CFSG.KC.LyReplay

end
