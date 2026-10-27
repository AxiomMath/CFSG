module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.ONVs

open CFSG.KC.Loop

@[expose] noncomputable def trW (L : Nat → Nat → Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih r x => ih (Nat.shiftRight r (nat_lit 4)) (L (Nat.land r (nat_lit 15)) x)) n

@[expose] noncomputable def wAt (L : Nat → Nat → Nat) (w x : Nat) : Nat :=
  trW L (Nat.land w (nat_lit 255)) (Nat.shiftRight w (nat_lit 8)) x

@[expose] noncomputable def letOK (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih r => bAnd(Nat.blt (Nat.land r (nat_lit 15)) (nat_lit 6),
      ih (Nat.shiftRight r (nat_lit 4)))) n

@[expose] noncomputable def wOK (w : Nat) : Bool :=
  letOK (Nat.land w (nat_lit 255)) (Nat.shiftRight w (nat_lit 8))

@[expose] noncomputable def key (L : Nat → Nat → Nat) (w : Nat) : Nat :=
  Nat.add (Nat.mul (wAt L w (nat_lit 2)) (nat_lit 245520)) (wAt L w (nat_lit 4))

@[expose] noncomputable def vsCheck (L : Nat → Nat → Nat) (N F E : Nat → Nat) : Bool :=
  bAnd(allBelow (nat_lit 6) (nat_lit 1) (fun l => Nat.beq (L l (nat_lit 0)) (nat_lit 0)),
  bAnd(allBelow (nat_lit 39) (nat_lit 1) (fun k => wOK (E k)),
  bAnd(Nat.beq (N (nat_lit 0)) (nat_lit 1), bAnd(Nat.beq (N (nat_lit 20)) (nat_lit 24),
  bAnd(Nat.beq (F (nat_lit 2)) (nat_lit 1), bAnd(Nat.beq (F (nat_lit 6)) (nat_lit 3),
  bAnd(Nat.beq (F (nat_lit 20)) (nat_lit 11), bAnd(Nat.beq (F (nat_lit 56)) (nat_lit 28),
  bAnd(Nat.beq (wAt L (E (nat_lit 0)) (nat_lit 2)) (N (nat_lit 2)),
  bAnd(Nat.beq (wAt L (E (nat_lit 1)) (nat_lit 6)) (N (nat_lit 6)),
  bAnd(Nat.beq (wAt L (E (nat_lit 2)) (nat_lit 56)) (N (nat_lit 56)),
  bAnd(allBelow (nat_lit 36) (nat_lit 1) (fun k =>
      Nat.beq (wAt L (E (Nat.add (nat_lit 3) k)) (nat_lit 20)) (nat_lit 20)),
    allBelow (nat_lit 35) (nat_lit 1) (fun k =>
      Nat.blt (key L (E (Nat.add (nat_lit 3) k))) (key L (E (Nat.add (nat_lit 4) k))))))))))))))))

end CFSG.KS.ONVs

end
