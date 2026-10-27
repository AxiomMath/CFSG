module

public import Certificates.Data.Kernel.Fi23Q.Defs
public import Certificates.Data.Kernel.Fi23R.Defs

public section

namespace CFSG.KC.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Pc3

@[expose] noncomputable def cwR (n W : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun m acc => List.cons (Nat.add (nat_lit 52)
      fld(W, Nat.mul (nat_lit 5) (Nat.sub (Nat.sub n (nat_lit 1)) m), nat_lit 31)) acc) n

@[expose] noncomputable def clsW (H G : Nat → Nat) (T : Nat → List Nat) (CR nQ q c n W : Nat) :
    Bool :=
  bAnd(Nat.blt q nQ, bAnd(Nat.blt c (nat_lit 4),
    bAnd(allN n (fun i => Nat.blt fld(W, Nat.mul (nat_lit 5) i, nat_lit 31) (nat_lit 24)),
      (fun w u => allN (nat_lit 6) fun b =>
        Nat.beq (wv G w (wv H u b)) (wv G (T c) (wv G w b)))
      (cwR n W) (nwR (nat_lit 13) (f32 CR q)))))

@[expose] noncomputable def tcB (G : Nat → Nat) (r k : Nat) : Bool :=
  allN (nat_lit 6) fun b => Nat.beq (tb G r b) (CFSG.KC.Fi23R.tA G k b)

end CFSG.KC.Fi23Q

end
