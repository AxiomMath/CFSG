module

public import Certificates.Data.Kernel.J2H2.Stable

public section

namespace CFSG.KD.J2H2

open CFSG.KC.Enum

@[expose] noncomputable def oN : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 55296) 1) 4095

@[expose] noncomputable def eN : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun r ih => Nat.lor ih (Nat.shiftLeft 1 (Nat.mul 13 r))) 12

@[expose] noncomputable def unitF (k u : Nat) : Nat :=
  Nat.shiftLeft eN (Nat.mul 144 (Nat.add (Nat.mul 128 k) u))

@[expose] noncomputable def mvI (cs : List Nat) (v O : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun col _ ih c => Nat.xor (Nat.mul col (Nat.land (Nat.shiftRight v c) O)) (ih (Nat.succ c))) cs 0

@[expose] noncomputable def wF (YC : List (List Nat)) (MTP GP PP O : Nat) (h fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih x => nIf(Nat.beq x 0, 0,
      (fun k p => Nat.xor (Nat.xor (mvI (getL [] YC k) (ih p) O)
        (unitF k (pg 7 127 MTP (Nat.add (Nat.mul 128 p) h)))) (unitF k p))
        (pg 2 3 GP x) (pg 7 127 PP x))) fuel

@[expose] noncomputable def cellF (YC : List (List Nat)) (MTP LMP GP PP O k b h : Nat) : Nat :=
  Nat.xor (Nat.xor (mvI (getL [] YC k) (wF YC MTP GP PP O h 8 b) O)
      (wF YC MTP GP PP O h 8 (pg 7 127 LMP (Nat.add (Nat.mul 128 k) b))))
    (Nat.xor (unitF k (pg 7 127 MTP (Nat.add (Nat.mul 128 b) h))) (unitF k b))

@[expose] noncomputable def cellK (YC : List (List Nat)) (MTP LMP GP PP O c : Nat) : Nat :=
  cellF YC MTP LMP GP PP O (Nat.mod c 3) (Nat.mod (Nat.div c 3) 128) (Nat.div c 384)

@[expose] noncomputable def maskL (YC : List (List Nat)) (MTP LMP GP PP O : Nat) (cs ms : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun ms => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ms)
    (fun c _ ih ms => List.rec (motive := fun _ => Bool) false
      (fun m ms' _ => bAnd(Nat.blt c 49152, bAnd(Nat.beq m (cellK YC MTP LMP GP PP O c), ih ms'))) ms) cs ms

@[expose] noncomputable def maskBlk (YC : List (List Nat)) (MTP LMP GP PP : Nat) (CKB MB : List (List Nat))
    (j : Nat) : Bool :=
  strictB oN (fun O => maskL YC MTP LMP GP PP O (getL [] CKB j) (getL [] MB j))

@[expose] noncomputable def maskAt (MB : List (List Nat)) (i : Nat) : Nat :=
  getL 0 (getL [] MB (Nat.div i 32)) (Nat.mod i 32)

@[expose] noncomputable def sumRefs (MB : List (List Nat)) (O : Nat) (refs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun q _ ih => Nat.xor (Nat.land (Nat.shiftRight (maskAt MB (Nat.div q 12)) (Nat.mod q 12)) O) ih) refs

@[expose] noncomputable def stepOK (MB : List (List Nat)) (O K piv : Nat) (refs : List Nat) : Bool :=
  bAnd(Nat.blt piv 4608, (fun m => Nat.beq (Nat.sub m (Nat.land m K)) (Nat.shiftLeft 1 (Nat.mul 12 piv)))
    (sumRefs MB O refs))

@[expose] noncomputable def echL (MB : List (List Nat)) (O : Nat) (st : List (List Nat)) (K Kend : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun K => Nat.beq K Kend)
    (fun s _ ih K => List.rec (motive := fun _ => Bool) false
      (fun piv refs _ => bAnd(stepOK MB O K piv refs,
        strictB (Nat.lor K (Nat.shiftLeft 1 (Nat.mul 12 piv))) ih)) s) st K

@[expose] noncomputable def echChunk (MB : List (List Nat)) (ST : List (List (List Nat))) (KS : List Nat)
    (i : Nat) : Bool :=
  strictB oN (fun O => echL MB O (getL [] ST i) (getL 0 KS i) (getL 0 KS (Nat.succ i)))

@[expose] noncomputable def initK (GP PP : Nat) (F : List Nat) : Nat :=
  Nat.lor (Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.lor ih
      (Nat.rec (motive := fun _ => Nat) 0 (fun r ih2 => Nat.lor ih2 (Nat.shiftLeft 1 (Nat.mul 12
        (Nat.add (Nat.mul 12 (Nat.add (Nat.mul 128 (pg 2 3 GP (Nat.succ i))) (pg 7 127 PP (Nat.succ i)))) r))))
        12)) 127)
    (List.rec (motive := fun _ => Nat) 0 (fun f _ ih => Nat.lor (Nat.shiftLeft 1 (Nat.mul 12 f)) ih) F)

@[expose] noncomputable def depthK (PP : Nat) : Bool :=
  allN 128 (fun x => Nat.beq (Nat.rec (motive := fun _ => Nat) x (fun _ ih => pg 7 127 PP ih) 7) 0)

@[expose] noncomputable def ksK (GP PP : Nat) (F : List Nat) (KS : List Nat) (ST : List (List (List Nat)))
    (YC : List (List Nat)) (A B : List Nat) (yW : List (List Nat)) : Bool :=
  bAnd(Nat.beq (getL 0 KS 0) (initK GP PP F), bAnd(Nat.beq (getL 0 KS 6) oN,
    bAnd(Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) ST) 6,
      allN 3 (fun k => lbeq (getL [] YC k) (matWordK A B (getL [] yW k))))))

end CFSG.KD.J2H2

end
