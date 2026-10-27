module

public import Certificates.Data.Kernel.Spor.Fi24Net

public section

namespace CFSG.KC.Fi24NetPt

open CFSG.KC.Loop CFSG.KC.Fi24Net

@[expose] noncomputable def swpK (d m q : Nat) : Nat :=
  nIf(Nat.beq (Nat.land (Nat.shiftRight m q) (nat_lit 1)) (nat_lit 1), Nat.add q d,
    nIf(Nat.ble d q,
      nIf(Nat.beq (Nat.land (Nat.shiftRight m (Nat.sub q d)) (nat_lit 1)) (nat_lit 1),
        Nat.sub q d, q),
      q))

@[expose] noncomputable def ptF (M : Nat → Nat) (q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q
    (fun j ih => strictN ih (fun y => swpK (ldist (Nat.sub (nat_lit 36) j))
      (M (Nat.sub (nat_lit 36) j)) y)) (nat_lit 37)

@[expose] noncomputable def ptR (M : Nat → Nat) (q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q
    (fun j ih => strictN ih (fun y => swpK (ldist j) (M j) y)) (nat_lit 37)

@[expose] noncomputable def letN (NW : Nat → Nat → Nat) (l x : Nat) : Nat :=
  nIf(Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0), ptF (NW (Nat.shiftRight l (nat_lit 1))) x,
    ptR (NW (Nat.shiftRight l (nat_lit 1))) x)

@[expose] noncomputable def planeL (NW : Nat → Nat → Nat) (l v : Nat) : Nat :=
  nIf(Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0), netF (NW (Nat.shiftRight l (nat_lit 1))) v,
    netR (NW (Nat.shiftRight l (nat_lit 1))) v)

end CFSG.KC.Fi24NetPt

end
