module

public import Certificates.Data.Kernel.Fi22Twist.Leaf

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

@[expose] noncomputable def djK (DF : Nat → Nat) (R j : Nat) : Bool :=
  strictB (rowR R (Nat.mul (nat_lit 3) j)) fun x =>
  strictB (rowR R (Nat.add (Nat.mul (nat_lit 3) j) (nat_lit 1))) fun y =>
  strictB (rowR R (Nat.add (Nat.mul (nat_lit 3) j) (nat_lit 2))) fun z =>
  bAnd(allN (nat_lit 3510) (fun i =>
      strictB (ap x i) fun xi =>
      strictB (ap y i) fun yi =>
      strictB (ap z i) fun zi =>
      bAnd(Nat.beq (ap x (ap x xi)) i, bAnd(Nat.beq (ap y (ap y yi)) i,
        bAnd(Nat.beq (ap z (ap z zi)) i, bAnd(Nat.beq (ap x yi) (ap y xi),
          bAnd(Nat.beq (ap x zi) (ap z xi), Nat.beq (ap y zi) (ap z yi))))))),
    allN (nat_lit 27) (fun e =>
      strictB (kAp (DF (Nat.add (Nat.mul (nat_lit 27) j) e)) baseKey) fun kd =>
      allN e (fun e' =>
        Bool.not (Nat.beq (kAp (DF (Nat.add (Nat.mul (nat_lit 27) j) e')) baseKey) kd))))

end CFSG.KC.Fi22Twist

end
