module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Fi22Cent

open CFSG.KC.Enum

@[expose] noncomputable def tApp (G : Nat → Nat → Nat) (par lab : Nat → Nat) (f : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ y => y)
    (fun _ ih p y => nIf(Nat.beq p 0, y, G (lab p) (ih (par p) y))) f

@[expose] noncomputable def tInv (Gi : Nat → Nat → Nat) (par lab : Nat → Nat) (f : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ y => y)
    (fun _ ih p y => nIf(Nat.beq p 0, y, ih (par p) (Gi (lab p) y))) f

@[expose] noncomputable def treeRow (G : Nat → Nat → Nat) (par lab dep : Nat → Nat) (p : Nat) :
    Bool :=
  Nat.beq p 0 || (Nat.blt (lab p) 3 && Nat.blt (par p) 3510 &&
    Nat.beq (Nat.succ (dep (par p))) (dep p) && Nat.ble (dep p) 64 && Nat.beq (G (lab p) (par p)) p)

@[expose] noncomputable def invRow (dp : Nat → Nat → Nat) (X w : Nat → Nat) (p : Nat) : Bool :=
  Nat.beq p 0 || Nat.beq p 1 || Nat.beq p (X 1) ||
    (Nat.blt (w p) 3510 && !(Nat.beq (dp p (X (dp p (X (w p))))) (w p)))

@[expose] noncomputable def cntN (T : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => Nat.add acc (nIf(Nat.beq (T x) x, nat_lit 1, nat_lit 0))) n

end CFSG.KC.Fi22Cent

end
