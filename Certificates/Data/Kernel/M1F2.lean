module

public import CFSG.Certificates.Kernel.Lie.CT.Core
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.M1F2

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def wsC (c : Nat) : Bool :=
  orB (Nat.beq c (nat_lit 32)) (andB (Nat.ble (nat_lit 9) c) (Nat.ble c (nat_lit 13)))

@[expose] noncomputable def ebit (c : Nat) : Nat :=
  nIf(andB (Nat.ble (nat_lit 48) c) (Nat.ble c (nat_lit 57)),
    Nat.land (Nat.sub c (nat_lit 48)) (nat_lit 1), nat_lit 0)

@[expose] noncomputable def m1Run (d M : Nat) (cs : List Char) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun ph k _ => andB (Nat.beq ph (nat_lit 1)) (Nat.ble (Nat.mul d d) k))
    (fun ch _ ih ph k acc => strictB k fun k => strictB acc fun acc => strictB (Char.toNat ch) fun c =>
      bIf(Nat.beq ph (nat_lit 0),
        bIf(Nat.beq c (nat_lit 10), ih (nat_lit 1) k acc, ih (nat_lit 0) k acc),
        bIf(wsC c, ih ph k acc,
          bIf(Nat.blt k (Nat.mul d d),
            strictB (Nat.lor (Nat.shiftRight acc (nat_lit 64)) (Nat.shiftLeft (ebit c) (Nat.mod k d))) fun r =>
              bIf(Nat.beq (Nat.succ (Nat.mod k d)) d,
                andB (Nat.beq r (fget M (Nat.div k d) d)) (ih ph (Nat.succ k) (nat_lit 0)),
                ih ph (Nat.succ k) (Nat.lor (Nat.shiftLeft r (nat_lit 64))
                  (Nat.land (Nat.succ k) (nat_lit 18446744073709551615)))),
            ih ph (Nat.succ k) acc))))
    cs

@[expose] noncomputable def m1Bind (cs : List Char) (d M : Nat) : Bool :=
  m1Run d M cs (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def rowF (d M i : Nat) : Nat := fget M i d

@[expose] noncomputable def vmF (d M v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => nIf(bit v k, Nat.xor (rowF d M k) acc, acc)) d

@[expose] noncomputable def mulF (d A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B =>
    orN d fun i => Nat.shiftLeft (vmF d B (rowF d A i)) (Nat.mul d i)

@[expose] noncomputable def idF (d : Nat) : Nat := orN d fun i => Nat.shiftLeft (pw2 i) (Nat.mul d i)

@[expose] noncomputable def powF (d X e nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (idF d)
    (fun i acc => strictN (mulF d acc acc) fun sq =>
      nIf(bit e (Nat.sub (Nat.sub nb (nat_lit 1)) i), mulF d sq X, sq)) nb

@[expose] noncomputable def orderK (d A B q nb : Nat) : Bool :=
  strictB (mulF d A B) fun X =>
    andB (Nat.beq (powF d X q nb) (idF d)) (notB (Nat.beq (rowF d X (nat_lit 0)) (nat_lit 1)))

end CFSG.KC.M1F2

end
