module

public import Init

public section

namespace CFSG.KD.Antiflag

@[expose] def swN (n c : Nat) : Nat := ((c >>> n) % 2 ^ n) ||| ((c % 2 ^ n) <<< n)

@[expose] def tvN (n i j c : Nat) : Nat :=
  c ^^^ (bif c.testBit j then 2 ^ i else 0) ^^^ (bif c.testBit (n + i) then 2 ^ (n + j) else 0)

@[expose] def evN (n : Nat) (d : Option (Nat × Nat)) : Nat → Nat :=
  d.elim (swN n) fun p => tvN n p.1 p.2

@[expose] def gDN (n : Nat) : List (Option (Nat × Nat)) :=
  none :: (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => j ≠ i).map fun j => some (i.val, j.val)

@[expose] def sDN (n : Nat) : List (Option (Nat × Nat)) :=
  none :: ((List.finRange n).filter fun i => i.val ≠ 0).flatMap fun i =>
    ((List.finRange n).filter fun j => j ≠ i ∧ j.val ≠ 0).map fun j => some (i.val, j.val)

@[expose] def gGN (n : Nat) : List (Nat → Nat) := (gDN n).map (evN n)

@[expose] def gSN (n : Nat) : List (Nat → Nat) := (sDN n).map (evN n)

@[expose] noncomputable def runCode (gs : List (Nat → Nat)) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih w c => bif w == 0 then c else gs.getD ((w &&& 31) - 1) id (ih (w >>> 5) c)) fuel

@[expose] noncomputable def decodeW (fuel : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih w => bif w == 0 then [] else ((w &&& 31) - 1) :: ih (w >>> 5)) fuel

@[expose] noncomputable def dotAux (n c m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k acc => xor acc (c.testBit k && c.testBit (n + k))) m

@[expose] noncomputable def dotB (n c : Nat) : Bool := dotAux n c n

@[expose] noncomputable def allLt (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && f k) m

@[expose] def lane (t c : Nat) : Nat := (t >>> (64 * c)) &&& (2 ^ 64 - 1)

@[expose] def baseN (n : Nat) : Nat := 1 + 2 ^ n

@[expose] def repN (n s : Nat) : Nat := [3 + 2 ^ n, 3 + 5 * 2 ^ n, 2 + 2 * 2 ^ n, 3 + 2 * 2 ^ n].getD s 0

@[expose] def fuelW : Nat := 16

@[expose] noncomputable def chkG (n tG : Nat) : Bool :=
  allLt (4 ^ n) fun c => !dotB n c || runCode (gGN n) fuelW (lane tG c) (baseN n) == c

@[expose] noncomputable def chkS (n tS : Nat) : Bool :=
  allLt (4 ^ n) fun c => !dotB n c || c == baseN n ||
    runCode (gSN n) fuelW (lane tS c >>> 2) (repN n (lane tS c &&& 3)) == c

@[expose] noncomputable def gTN (n tG s : Nat) : List (Nat → Nat) :=
  gSN n ++ [runCode (gGN n) fuelW (lane tG (repN n s))]

@[expose] noncomputable def chkT (n tG s tT : Nat) : Bool :=
  allLt (4 ^ n) fun c => !dotB n c || runCode (gTN n tG s) fuelW (lane tT c) (baseN n) == c

end CFSG.KD.Antiflag
