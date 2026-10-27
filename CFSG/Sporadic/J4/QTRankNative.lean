module

public import CFSG.Sporadic.J4.QTNative
public import CFSG.Sporadic.J4.QTRankData

public section

namespace CFSG.Sporadic.J4.QT

@[expose] def actT (t : List Nat) (c : Nat) : Nat := rowsXor (fun j => t.getD j 0) 11 c

@[expose] def idT : List Nat := (List.range 11).map fun j => 2 ^ j

@[expose] def compT (t t' : List Nat) : List Nat := t'.map (actT t)

@[expose] def letterTab (ℓ : Int) : List Nat := (List.range 11).map (letterRow ℓ)

@[expose] def wordT (w : List Int) : List Nat := (w.map letterTab).foldr compT idT

@[expose] def kTab (i : Nat) : List Nat := wordT (kWords.getD i [])

@[expose] def kInvTab (i : Nat) : List Nat := wordT (invWord (kWords.getD i []))

@[expose] def seqT (s : List Nat) : List Nat := (s.map kTab).foldr compT idT

@[expose] def pcSeq (e : Nat) : List Nat :=
  (List.range 10).flatMap fun j => if e.testBit j then pcSeqs.getD j [] else []

@[expose] def tabL : List (List Nat) := (List.range 1024).map fun e => seqT (pcSeq e)

@[expose] def lenOK (t : List Nat) : Bool := t.length == 11 && t.all (· < 2048)

@[expose] def fixCount (t : List Nat) : Nat := ((List.range 2048).filter fun c => actT t c == c).length

end CFSG.Sporadic.J4.QT
