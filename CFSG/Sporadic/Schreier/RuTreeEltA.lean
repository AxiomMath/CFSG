module

public import CFSG.Sporadic.Schreier.RuCheckTreeInputs

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruTGenA (k : ℕ) : Array ℕ := if k = 0 then ruA0A else ruA1A

@[expose] def ruTGenInvA (k : ℕ) : Array ℕ := if k = 0 then ruInv ruA0A else ruInv ruA1A

@[expose] def ruTEltA : ℕ → ℕ → Array ℕ
  | 0, _ => idA 4060
  | f + 1, j => if j = 0 then idA 4060 else
      compA 4060 (ruTGenA ruTreeLab[j]!) (ruTEltA f ruTreePar[j]!)

@[expose] def ruTEltInvA : ℕ → ℕ → Array ℕ
  | 0, _ => idA 4060
  | f + 1, j => if j = 0 then idA 4060 else
      compA 4060 (ruTEltInvA f ruTreePar[j]!) (ruTGenInvA ruTreeLab[j]!)

@[expose] def ruTZA (j : ℕ) : Array ℕ :=
  compA 4060 (compA 4060 (ruTEltA 64 j) ruZA) (ruTEltInvA 64 j)

@[expose] def ruTreeIdx : Std.HashMap (List ℕ) ℕ :=
  (Array.range 593775).foldl (fun m j => m.insert ruTreeSets[j]! j)
    (Std.HashMap.emptyWithCapacity 1048576)

@[expose] def ruZIdx (t : Array ℕ) : ℕ := (ruTreeIdx[fixedList 4060 t]?).getD 0

@[expose] def ruZWit (t : Array ℕ) : Bool := eqA 4060 (ruTZA (ruZIdx t)) t

end CFSG.Sporadic.RuSchreier
