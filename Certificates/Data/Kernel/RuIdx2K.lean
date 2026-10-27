module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Kc3E16K

public section

namespace CFSG.KC.RuIdx2

open CFSG.KC.Enum CFSG.KC.Kc3K

@[expose] noncomputable def wp (LC : Nat → Nat) (W q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun k ih q => strictN (pg (nat_lit 12) (nat_lit 4095)
      (LC fld(W, Nat.add (nat_lit 8) (Nat.shiftLeft k (nat_lit 2)), nat_lit 15)) q) ih)
    (Nat.land W (nat_lit 255)) q

@[expose] noncomputable def wpi (LC IL : Nat → Nat) (W q : Nat) : Nat :=
  (fun n => Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun k ih q => strictN (pg (nat_lit 12) (nat_lit 4095)
      (LC (IL fld(W, Nat.add (nat_lit 8)
        (Nat.shiftLeft (Nat.sub (Nat.sub n (nat_lit 1)) k) (nat_lit 2)), nat_lit 15))) q) ih)
    n q) (Nat.land W (nat_lit 255))

@[expose] noncomputable def el (LC IL RG : Nat → Nat) (nr X l q : Nat) : Nat :=
  nIf(Nat.blt l nr, wp LC (RG l) q,
    nIf(Nat.blt l (Nat.add nr nr), wpi LC IL (RG (Nat.sub l nr)) q,
      nIf(Nat.beq l (Nat.add nr nr), wp LC X q, wpi LC IL X q)))

@[expose] noncomputable def ep (LC IL RG : Nat → Nat) (nr X E q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun k ih q => strictN (el LC IL RG nr X
      fld(E, Nat.add (nat_lit 8) (Nat.shiftLeft k (nat_lit 2)), nat_lit 15) q) ih)
    (Nat.land E (nat_lit 255)) q

@[expose] noncomputable def par (vm x : Nat) : Nat :=
  (fun y => Nat.land (Nat.xor y (Nat.xor (Nat.shiftRight y (nat_lit 1))
    (Nat.shiftRight y (nat_lit 2)))) (nat_lit 1)) (Nat.land x vm)

@[expose] noncomputable def edgeK (LC IL RG RW : Nat → Nat) (B : List Nat) (nr n it : Nat) : Bool :=
  strictB (Nat.land it (nat_lit 4095)) fun d => bAnd(Nat.blt d n,
    strictB (RW n) fun X => strictB (RW d) fun Y =>
      strictB (Nat.shiftRight it (nat_lit 12)) fun E =>
        B.all fun b => Nat.beq (wp LC Y b) (ep LC IL RG nr X E b))

@[expose] noncomputable def allIdx (f : Nat → Nat → Bool) (lo : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun it _ ih i => bAnd(f i it, strictB (Nat.succ i) ih)) L lo

@[expose] noncomputable def memN (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) L

@[expose] noncomputable def tp (LC : Nat → Nat) (o tau q : Nat) : Nat :=
  nIf(Nat.beq o (nat_lit 1), pg (nat_lit 12) (nat_lit 4095) (LC tau) q, q)

@[expose] noncomputable def matchK (LC RW XW PS TF eu ev : Nat → Nat) (B : List Nat)
    (nR vm tau p it : Nat) : Bool :=
  strictB (Nat.land it (nat_lit 4095)) fun i =>
    strictB fld(it, nat_lit 12, nat_lit 16383) fun k1 =>
      strictB (Nat.shiftRight it (nat_lit 26)) fun k2 =>
        bAnd(Nat.blt i nR, bAnd(Nat.blt k2 (nat_lit 16384),
          bAnd(Nat.beq (par vm (PS k1)) (nat_lit 0), bAnd(Nat.beq (par vm (PS k2)) (nat_lit 0),
            strictB (eu k1) fun u1 => strictB (ev k1) fun v1 =>
              strictB (eu k2) fun u2 => strictB (ev k2) fun v2 =>
                strictB (RW i) fun X => strictB (XW (Nat.shiftRight p (nat_lit 1))) fun Y =>
                  B.all fun b => Nat.beq (wp LC X b)
                    (exK (nat_lit 12) (nat_lit 4095) TF u1 v1
                      (tp LC (Nat.land p (nat_lit 1)) tau
                        (wp LC Y (exK (nat_lit 12) (nat_lit 4095) TF u2 v2 b))))))))

@[expose] noncomputable def witK (LC IL RG RW PS TF eu ev : Nat → Nat) (B : List Nat)
    (nr vm WX WE WK : Nat) : Bool :=
  strictB (Nat.land WK (nat_lit 16383)) fun kr => strictB (Nat.shiftRight WK (nat_lit 14)) fun kt =>
    bAnd(Nat.blt kt (nat_lit 16384),
      bAnd(Nat.beq (par vm (PS kr)) (nat_lit 0), bAnd(Nat.beq (par vm (PS kt)) (nat_lit 1),
        strictB (eu kr) fun ur => strictB (ev kr) fun vr =>
          strictB (eu kt) fun ut => strictB (ev kt) fun vt => strictB (RW (nat_lit 0)) fun X =>
            B.all fun b => bAnd(Nat.beq (wp LC WX b) (ep LC IL RG nr X WE b),
              Nat.beq (wp LC WX (exK (nat_lit 12) (nat_lit 4095) TF ur vr b))
                (exK (nat_lit 12) (nat_lit 4095) TF ut vt (wp LC WX b))))))

@[expose] noncomputable def labK (PS : Nat → Nat) (tg : Nat → Nat → Nat) (k : Nat) : Bool :=
  strictB (PS k) fun s =>
    bAnd(Nat.beq (PS (tg (nat_lit 0) k)) (Nat.xor s (nat_lit 1)),
      bAnd(Nat.beq (PS (tg (nat_lit 1) k)) (Nat.xor s (nat_lit 2)),
        Nat.beq (PS (tg (nat_lit 2) k)) (Nat.xor s (nat_lit 4))))

@[expose] noncomputable def letK (LC IL : Nat → Nat) (n c : Nat) : Bool :=
  strictB (LC c) fun A => strictB (LC (IL c)) fun Ai =>
    allN n fun q => Nat.beq (pg (nat_lit 12) (nat_lit 4095) Ai (pg (nat_lit 12) (nat_lit 4095) A q)) q

end CFSG.KC.RuIdx2

end
