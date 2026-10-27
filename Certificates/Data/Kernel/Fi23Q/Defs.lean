module

public import Certificates.Data.Kernel.Fi23K.Defs
public import Certificates.Data.Kernel.Pc3.Coll

public section

namespace CFSG.KC.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Pc3

@[expose] noncomputable def gTab (H G : Nat → Nat) (k : Nat) (w : List Nat) (lo c : Nat) : Bool :=
  allN c fun l => strictB (Nat.add lo l) fun x => Nat.beq (tb H k x) (wv G w x)

@[expose] noncomputable def cTab (H : Nat → Nat) (k i j lo c : Nat) : Bool :=
  allN c fun l => strictB (Nat.add lo l) fun x => strictB (tb H k x) fun y =>
    bAnd(Nat.blt y (nat_lit 31671), Nat.beq (tb H j (tb H i y)) (tb H i (tb H j x)))

@[expose] noncomputable def nwR (n u : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun m acc => (fun k => (fun e =>
      Bool.rec (motive := fun _ => List Nat)
        (Bool.rec (motive := fun _ => List Nat) (List.cons k (List.cons k acc)) (List.cons k acc)
          (Nat.beq e (nat_lit 1)))
        acc (Nat.beq e (nat_lit 0))) (dg u k)) (Nat.sub (Nat.sub n (nat_lit 1)) m)) n

@[expose] noncomputable def eqH (H : Nat → Nat) (u v : List Nat) : Bool :=
  allN (nat_lit 6) fun b => Nat.beq (wv H u b) (wv H v b)

@[expose] noncomputable def relB (H : Nat → Nat) (n PW CJ : Nat) : Bool :=
  bAnd(allN n fun k => eqH H [k, k, k] (nwR n (f32 PW k)),
    allN n fun i => allN n fun j => bIf(Nat.blt i j,
      eqH H [j, i] (List.cons i (nwR n (f32 CJ (Nat.add (Nat.shiftLeft i (nat_lit 4)) j)))), true))

end CFSG.KC.Fi23Q

end
