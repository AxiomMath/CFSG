module

public section

namespace CFSG.KC.LyY

@[expose] def covN (f : Nat → Nat) (K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => Nat.lor ih (Nat.shiftLeft 1 (f k))) K

end CFSG.KC.LyY

end
