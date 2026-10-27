module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Misc.PtOrbF

public section

namespace CFSG.KC.Fi22Pump

open CFSG.KC.Enum CFSG.KC.PtOrb

@[expose] noncomputable def sigC (S A G : Nat → Nat) : Bool :=
  allN (nat_lit 3510) fun x => Nat.beq (S (A x)) (G (S x))

@[expose] noncomputable def cntN (T : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => Nat.add acc (nIf(Nat.beq (T x) x, nat_lit 1, nat_lit 0))) n

@[expose] noncomputable def cntF (T : Nat → Nat) : Nat := cntN T (nat_lit 3510)

@[expose] noncomputable def commC (Y X : Nat → Nat) : Bool :=
  allN (nat_lit 3510) fun x => Nat.beq (Y (X x)) (X (Y x))

@[expose] noncomputable def orbC (f : Nat → Nat → Nat) (k r x c : Nat) : Bool :=
  strictB (closeF f k (nat_lit 3510) r (Nat.shiftLeft (nat_lit 1) x)) fun s =>
    bAnd(closedF f k (nat_lit 3510) s, Nat.beq (popF s (nat_lit 3510)) c)

@[expose] noncomputable def rowF (T Q : Nat → Nat) (keys : List Nat) (isId : Bool) : Bool :=
  keys.any (fun p => !(Nat.beq (T (T (T p))) p)) || isId ||
    (Nat.beq (cntF T) (nat_lit 126) && !(commC T Q))

end CFSG.KC.Fi22Pump

end
