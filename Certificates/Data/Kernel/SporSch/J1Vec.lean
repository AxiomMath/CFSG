module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch.J1Vec

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def vf (v j : Nat) : Nat := fld(v, Nat.mul (nat_lit 4) j, nat_lit 15)

@[expose] noncomputable def rowK (v : Nat) (x : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (nat_lit 7))
    (fun a _ ih j => bAnd(Nat.blt a (nat_lit 11), bAnd(Nat.beq a (vf v j), ih (Nat.succ j)))) x

@[expose] noncomputable def vbindFrom (VT : Nat → Nat) (L : List (List Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun i N => Nat.beq i N)
    (fun x _ ih i N => strictB (VT i) (fun v =>
      bAnd(Nat.beq (Nat.shiftRight v (nat_lit 28)) (nat_lit 0),
        bAnd(rowK v x (nat_lit 0), ih (Nat.succ i) N)))) L

@[expose] noncomputable def vbindK (L : List (List Nat)) (VT : Nat → Nat) (N : Nat) : Bool :=
  vbindFrom VT L (nat_lit 0) N

@[expose] noncomputable def sortFrom (VT : Nat → Nat) (N : Nat) (O : List Nat) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun c _ _ => Nat.beq c N)
    (fun k _ ih c M prev => strictB (VT k) (fun v =>
      bAnd(Nat.blt k N, bAnd(bIf(hasBit M k, false, true), bAnd(Nat.blt prev (Nat.succ v),
        strictB (Nat.lor M (Nat.shiftLeft (nat_lit 1) k)) (fun M' =>
          ih (Nat.succ c) M' (Nat.succ v))))))) O

@[expose] noncomputable def sortK (VT : Nat → Nat) (O : List Nat) (N : Nat) : Bool :=
  sortFrom VT N O (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def nzK (VT : Nat → Nat) (N : Nat) : Bool :=
  allN N (fun i => strictB (VT i) (fun v =>
    bAnd(Nat.beq (Nat.shiftRight v (nat_lit 28)) (nat_lit 0), bAnd(Nat.blt (nat_lit 0) v,
      allN (nat_lit 7) (fun j => Nat.blt (vf v j) (nat_lit 11))))))

@[expose] noncomputable def me (MP r c : Nat) : Nat :=
  fld(MP, Nat.mul (nat_lit 4) (Nat.add (Nat.mul (nat_lit 7) r) c), nat_lit 15)

@[expose] noncomputable def dotK (MP v r : Nat) : Nat :=
  Nat.mod (foldN (nat_lit 7) (fun c s => Nat.add s (Nat.mul (me MP r c) (vf v c))) (nat_lit 0))
    (nat_lit 11)

@[expose] noncomputable def mulK (MP v : Nat) : Nat :=
  foldN (nat_lit 7) (fun r s => Nat.lor s (Nat.shiftLeft (dotK MP v r) (Nat.mul (nat_lit 4) r)))
    (nat_lit 0)

@[expose] noncomputable def mvK (MP : Nat) (VT : Nat → Nat) (P N : Nat) : Bool :=
  allN N (fun i => Nat.beq (mulK MP (VT i)) (VT (pg 12 (mask 12) P i)))

end CFSG.KS.SporSch.J1Vec

end
