module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Text

public section

namespace CFSG.KC.Fendel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Text

@[expose] noncomputable def hexTabRun (w : Nat) (cs : List Char) : List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Nat → Bool)
    (fun L t _ => bAnd(Nat.beq t (nat_lit 0),
      List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L))
    (fun ch _ ih L t v => strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
      strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) w,
          List.rec (motive := fun _ => Bool) false
            (fun x xs _ => bAnd(Nat.beq v' x, ih xs (nat_lit 0) (nat_lit 0))) L,
          ih L (Nat.succ t) v')),
      false)))
    cs

@[expose] noncomputable def hexTabK (w : Nat) (L : List Nat) (cs : List Char) : Bool :=
  bAnd(Nat.blt (nat_lit 0) w, hexTabRun w cs L (nat_lit 0) (nat_lit 0))

@[expose] noncomputable def trAt (LR TR : Nat → Nat) (i k : Nat) : Nat :=
  TR (Nat.add (roff 276 (Nat.mul 276 9) (LR i)) k)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 276 9 (mask 9) p q

@[expose] noncomputable def prodOK (p q r : Nat) : Bool :=
  compEqK 276 9 (mask 9) (Nat.mul 276 9) p q r

@[expose] noncomputable def prod3 (LR TR : Nat → Nat) (i0 i1 i2 : Nat) : Nat :=
  pc (pc (trAt LR TR 0 i0) (trAt LR TR 1 i1)) (trAt LR TR 2 i2)

@[expose] noncomputable def prod3OK (LR TR : Nat → Nat) (i0 i1 i2 : Nat) : Bool :=
  bAnd(Nat.blt i0 (rcnt (LR 0)), bAnd(Nat.blt i1 (rcnt (LR 1)), bAnd(Nat.blt i2 (rcnt (LR 2)),
  bAnd(prodOK (trAt LR TR 0 i0) (trAt LR TR 1 i1) (pc (trAt LR TR 0 i0) (trAt LR TR 1 i1)),
    prodOK (pc (trAt LR TR 0 i0) (trAt LR TR 1 i1)) (trAt LR TR 2 i2) (prod3 LR TR i0 i1 i2)))))

@[expose] noncomputable def prod4 (LR TR : Nat → Nat) (i0 i1 i2 i3 : Nat) : Nat :=
  pc (prod3 LR TR i0 i1 i2) (trAt LR TR 3 i3)

@[expose] noncomputable def prod4OK (LR TR : Nat → Nat) (i0 i1 i2 i3 : Nat) : Bool :=
  bAnd(prod3OK LR TR i0 i1 i2, bAnd(Nat.blt i3 (rcnt (LR 3)),
    prodOK (prod3 LR TR i0 i1 i2) (trAt LR TR 3 i3) (prod4 LR TR i0 i1 i2 i3)))

@[expose] noncomputable def ix0 (wv : Nat) : Nat := (wv / 16 ^ 5) % 256
@[expose] noncomputable def ix1 (wv : Nat) : Nat := (wv / 16 ^ 3) % 256
@[expose] noncomputable def ix2 (wv : Nat) : Nat := (wv / 16) % 256
@[expose] noncomputable def ix3 (wv : Nat) : Nat := wv % 16

@[expose] noncomputable def hOf (LRm TRm : Nat → Nat) (wv : Nat) : Nat :=
  prod4 LRm TRm (ix0 wv) (ix1 wv) (ix2 wv) (ix3 wv)

@[expose] noncomputable def hOK (LRm TRm TRIm : Nat → Nat) (BPm wv X Y : Nat) : Bool :=
  strictB (hOf LRm TRm wv) (fun H =>
  bAnd(prod4OK LRm TRm (ix0 wv) (ix1 wv) (ix2 wv) (ix3 wv),
  bAnd(invEqK 276 9 (mask 9) (Nat.mul 276 9) H (pinvS 276 9 (mask 9) H),
  bAnd(Nat.beq (Nat.shiftRight H (Nat.mul 276 9)) (nat_lit 0),
  bAnd(siftK 276 9 (mask 9) (Nat.mul 276 9) (pidn 276 9) LRm TRIm BPm (nat_lit 4) (nat_lit 0) H,
  bAnd(prodOK H X (pc H X), bAnd(prodOK Y H (pc Y H), Nat.beq (pc H X) (pc Y H))))))))

@[expose] noncomputable def witK (LRt TRt LRm TRm TRIm : Nat → Nat) (BPm A Z T wv a b c : Nat) :
    Bool :=
  strictB (prod3 LRt TRt a b c) (fun X =>
  bAnd(prod3OK LRt TRt a b c,
  bIf(Nat.beq X (pidn 276 9), true,
  bIf(bAnd(prodOK X X (pc X X), neIdK 276 9 (mask 9) (Nat.mul 276 9) (pidn 276 9) (pc X X)), true,
  bIf(bAnd(Nat.beq (Nat.div wv 268435456) 0, Nat.beq X Z), true,
  bIf(bAnd(Nat.beq (Nat.div wv 268435456) 1, hOK LRm TRm TRIm BPm wv X A), true,
    bAnd(Nat.beq (Nat.div wv 268435456) 2, hOK LRm TRm TRIm BPm wv X T)))))))

@[expose] noncomputable def witAll (LRt TRt LRm TRm TRIm : Nat → Nat) (BPm A Z T : Nat)
    (W : List Nat) (a₀ na : Nat) : Bool :=
  allN na (fun da => strictB (Nat.add a₀ da) (fun a => allN 4 (fun b => allN 2 (fun c =>
    witK LRt TRt LRm TRm TRIm BPm A Z T (lget W (Nat.add (Nat.mul (Nat.add (Nat.mul a 4) b) 2) c))
      a b c))))

end CFSG.KC.Fendel

end
