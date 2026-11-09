module

public import Certificates.Data.Kernel.Spor.ONLineKW
public import Certificates.Data.Kernel.Spor.ONVecK

public section

namespace CFSG.KS.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def ptsV (X Y : Nat → Nat) (pre : Nat → Nat → Nat → Bool) (lo : Nat)
    (fin : Nat → Nat → Bool) (k : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun xx xy => fin xx xy)
    (fun k ih xx xy =>
      strictB (Nat.add lo k) fun h => strictB (X h) fun x => strictB (Y h) fun y =>
        bAnd(pre h x y,
          strictB (Nat.add x (Nat.shiftLeft xx (nat_lit 512))) fun xx' =>
          strictB (Nat.add y (Nat.shiftLeft xy (nat_lit 512))) fun xy' =>
            ih xx' xy'))
    k

@[expose] noncomputable def finE (L : List Nat) (cnt xx xy : Nat) : Bool :=
  strictB (rep (nat_lit 1) cnt) fun E => strictB (rep (mask (nat_lit 256)) cnt) fun LO =>
  strictB (Nat.land xx LO) fun XP => strictB (Nat.land (Nat.shiftRight xx (nat_lit 256)) LO) fun XM =>
    wmvL E XP XM (Nat.land xy LO) (Nat.land (Nat.shiftRight xy (nat_lit 256)) LO) L
      (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def finP (L : List Nat) (cnt xx xy : Nat) : Bool :=
  strictB (rep (nat_lit 1) cnt) fun E => strictB (rep (mask (nat_lit 256)) cnt) fun LO =>
  strictB (Nat.land xx LO) fun XP => strictB (Nat.land (Nat.shiftRight xx (nat_lit 256)) LO) fun XM =>
    wmvLT E XP XM (pmW E LO (Nat.land xy LO) (Nat.land (Nat.shiftRight xy (nat_lit 256)) LO)) L
      (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def sigRangeW (KS K : Nat → Nat) (LT : List Nat) (lo cnt : Nat) : Bool :=
  ptsV (key K) (key KS) (fun _ x y => bAnd(canon x, canon y)) lo (finE LT cnt) cnt (nat_lit 0)
    (nat_lit 0)

end CFSG.KS.ONW

end
