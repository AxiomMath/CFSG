module

public import Certificates.Data.E6TableT
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictN strictB)
open Certificates.Data.E6TableT (Vec dot iform reps)

@[expose] noncomputable def rowOf (GR a : Nat) : Nat :=
  fld(GR, Nat.mul (nat_lit 216) a,
    nat_lit 105312291668557186697918027683670432318895095400549111254310977535)

@[expose] noncomputable def lane (r j : Nat) : Nat := fld(r, Nat.mul (nat_lit 3) j, nat_lit 7)

@[expose] noncomputable def flOf (FL i : Nat) : Nat :=
  fld(FL, Nat.mul (nat_lit 30) i, nat_lit 1073741823)

@[expose] noncomputable def bitF (FL j b : Nat) : Bool :=
  Nat.beq fld(flOf FL j, b, nat_lit 1) (nat_lit 1)

@[expose] noncomputable def slotOf (N i : Nat) : Nat :=
  fld(N, Nat.mul (nat_lit 140) i, nat_lit 1393796574908163946345982392040522594123775)

@[expose] noncomputable def lm (a : Nat) : Nat := Nat.shiftLeft (nat_lit 7) (Nat.mul (nat_lit 3) a)

@[expose] noncomputable def zt (r m : Nat) : Bool := Nat.beq (Nat.land r m) (nat_lit 0)

@[expose] noncomputable def sumP (n : Nat) (f : Nat → Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih p => strictN p fun p => strictN (Nat.land p (nat_lit 127)) fun e =>
      nIf(Nat.beq e (nat_lit 0), nat_lit 0,
        strictN (Nat.sub e (nat_lit 1)) fun a =>
          Nat.add (f a) (ih (Nat.shiftRight p (nat_lit 7))))) n

@[expose] noncomputable def packF (n : Nat) (pr : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN (Nat.sub (Nat.sub n j) (nat_lit 1)) fun i =>
      nIf(pr i, Nat.lor (Nat.shiftLeft acc (nat_lit 7)) (Nat.succ i), acc)) n

@[expose] noncomputable def enumK (GR L0 N1 N2 N3 N4 N5 : Nat)
    (leaf : Nat → Nat → Nat → Nat → Nat → Nat → Nat) : Nat :=
  sumP (nat_lit 72) (fun a0 =>
    sumP (nat_lit 20) (fun a2 =>
      strictN (Nat.lor (lm a0) (lm a2)) fun m1 =>
      sumP (nat_lit 20) (fun a3 =>
        nIf(zt (rowOf GR a3) (lm a0),
          sumP (nat_lit 20) (fun a1 =>
            nIf(zt (rowOf GR a1) m1,
              strictN (Nat.lor m1 (lm a1)) fun m4 =>
              strictN (Nat.lor m4 (lm a3)) fun m5 =>
              sumP (nat_lit 20) (fun a4 =>
                nIf(zt (rowOf GR a4) m4,
                  sumP (nat_lit 20) (fun a5 =>
                    nIf(zt (rowOf GR a5) m5, leaf a0 a1 a2 a3 a4 a5, nat_lit 0))
                    (slotOf N5 a4),
                  nat_lit 0))
                (slotOf N4 a3),
              nat_lit 0))
            (slotOf N1 a3),
          nat_lit 0))
        (slotOf N3 a2))
      (slotOf N2 a0))
    L0

@[expose] noncomputable def allIdx (f : Nat → Vec → Bool) : List Vec → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => bAnd(f i x, ih (Nat.succ i)))

@[expose] noncomputable def rowCalc (x : Vec) : List Vec → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun y _ ih => Nat.lor (Int.toNat (Int.emod (iform x y) 8)) (Nat.shiftLeft ih (nat_lit 3)))

@[expose] noncomputable def resFlag (x v : Vec) (l : Nat) : Bool :=
  (dot x v - 2 * v.getD l 0) % 3 == 0

@[expose] noncomputable def repFlags (x v : Vec) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l _ ih =>
      Nat.lor (bif resFlag x v l then nat_lit 1 else nat_lit 0) (Nat.shiftLeft ih (nat_lit 1)))
    [0, 1, 2, 3, 4, 5]

@[expose] noncomputable def flagsCalc (x : Vec) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun v _ ih => Nat.lor (repFlags x v) (Nat.shiftLeft ih (nat_lit 6))) reps

@[expose] noncomputable def grOK (R : List Vec) (GR FL : Nat) : Bool :=
  bAnd(Nat.beq R.length (nat_lit 72),
    allIdx (fun i x => bAnd(Nat.beq (rowOf GR i) (rowCalc x R), Nat.beq (flOf FL i) (flagsCalc x)))
      R (nat_lit 0))

@[expose] noncomputable def lvlOK (GR FL b N : Nat) : Bool :=
  CFSG.KC.Loop.allBelow (nat_lit 72) (nat_lit 2) fun i => strictB (rowOf GR i) fun r =>
    Nat.beq (slotOf N i)
      (packF (nat_lit 72) fun j => bAnd(Nat.beq (lane r j) (nat_lit 7), bitF FL j b))

@[expose] noncomputable def nbOK (GR FL k L0 N1 N2 N3 N4 N5 : Nat) : Bool :=
  strictB (Nat.mul (nat_lit 6) k) fun b =>
    bAnd(Nat.beq L0 (packF (nat_lit 72) fun j => bitF FL j b),
    bAnd(lvlOK GR FL (Nat.add b (nat_lit 1)) N1,
    bAnd(lvlOK GR FL (Nat.add b (nat_lit 2)) N2,
    bAnd(lvlOK GR FL (Nat.add b (nat_lit 3)) N3,
    bAnd(lvlOK GR FL (Nat.add b (nat_lit 4)) N4,
      lvlOK GR FL (Nat.add b (nat_lit 5)) N5)))))

@[expose] noncomputable def repOK (GR FL k L0 N1 N2 N3 N4 N5 cnt : Nat) : Bool :=
  bAnd(nbOK GR FL k L0 N1 N2 N3 N4 N5,
    Nat.beq (enumK GR L0 N1 N2 N3 N4 N5 fun _ _ _ _ _ _ => nat_lit 1) cnt)

end CFSG.KC.E6TT

end
