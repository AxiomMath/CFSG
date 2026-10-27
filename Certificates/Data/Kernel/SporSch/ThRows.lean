module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.CFSGNative.Th.Core
public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.Sporadic.Th.Native

@[expose] noncomputable def v4N (x : V4) : Nat :=
  V4.rec (motive := fun _ => Nat) (fun a b c d => Nat.lor (UInt64.toNat a)
    (Nat.lor (Nat.shiftLeft (UInt64.toNat b) (nat_lit 64))
      (Nat.lor (Nat.shiftLeft (UInt64.toNat c) (nat_lit 128))
        (Nat.shiftLeft (UInt64.toNat d) (nat_lit 192))))) x

@[expose] noncomputable def v4From (R : Nat → Nat) (l : List V4) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => strictB (R i) (fun r => bAnd(Nat.beq (v4N x) r,
      bAnd(Nat.blt r (Nat.shiftLeft (nat_lit 1) (nat_lit 248)), ih (Nat.succ i))))) l

@[expose] noncomputable def lenV (l : List V4) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def v4BindK (l : List V4) (R : Nat → Nat) : Bool :=
  bAnd(Nat.beq (lenV l) (nat_lit 248), v4From R l (nat_lit 0))

@[expose] noncomputable def vmT (Y : Nat → Nat) (v : Nat) : Nat :=
  foldN (nat_lit 248) (fun j acc =>
    nIf(Nat.blt (nat_lit 0) (Nat.land v (Nat.shiftLeft (nat_lit 1) j)), Nat.xor acc (Y j), acc))
    (nat_lit 0)

@[expose] noncomputable def idBlkK (X Y : Nat → Nat) (lo len : Nat) : Bool :=
  allBlk lo (fun i => Nat.beq (vmT Y (X i)) (Nat.shiftLeft (nat_lit 1) i)) len

@[expose] noncomputable def par248 (x : Nat) : Nat :=
  foldN (nat_lit 248) (fun j acc => Nat.xor acc (Nat.land (Nat.shiftRight x j) (nat_lit 1)))
    (nat_lit 0)

@[expose] noncomputable def colK (R : Nat → Nat) (x : Nat) : Nat :=
  foldN (nat_lit 248) (fun i acc => nIf(Nat.beq (par248 (Nat.land (R i) x)) (nat_lit 1),
    Nat.lor acc (Nat.shiftLeft (nat_lit 1) i), acc)) (nat_lit 0)

@[expose] noncomputable def canonN (a b : Nat) : Nat :=
  strictN (Nat.xor a b) (fun s =>
  strictN (nIf(Nat.blt b a, b, a)) (fun x => strictN (nIf(Nat.blt b a, a, b)) (fun y =>
  strictN (nIf(Nat.blt s y, s, y)) (fun y' =>
    nIf(Nat.blt y' x, Nat.lor y' (Nat.shiftLeft x (nat_lit 256)),
      Nat.lor x (Nat.shiftLeft y' (nat_lit 256)))))))

@[expose] noncomputable def wsT (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 32), true, bIf(Nat.beq c (nat_lit 9), true, bIf(Nat.beq c (nat_lit 10), true,
    bIf(Nat.beq c (nat_lit 13), true, bIf(Nat.beq c (nat_lit 11), true, Nat.beq c (nat_lit 12))))))

@[expose] noncomputable def parT (c : Nat) : Nat :=
  nIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
    Nat.land (Nat.sub c (nat_lit 48)) (nat_lit 1), nat_lit 0)

@[expose] noncomputable def thPayRun (R : Nat → Nat) (cs : List Char) : Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun _ i _ acc => bIf(Nat.blt i (nat_lit 248),
      bAnd(Nat.beq (R i) acc,
        allBlk (Nat.succ i) (fun r => Nat.beq (R r) (nat_lit 0)) (Nat.sub (nat_lit 247) i)),
      true))
    (fun ch _ ih ph i j acc => strictB (Char.toNat ch) (fun c =>
      bIf(Nat.beq ph (nat_lit 0),
        bIf(Nat.beq c (nat_lit 10), ih (nat_lit 1) i j acc, ih (nat_lit 0) i j acc),
        bIf(wsT c, ih (nat_lit 1) i j acc,
          bIf(Nat.blt i (nat_lit 248),
            strictB (Nat.lor acc (Nat.shiftLeft (parT c) j)) (fun acc' =>
              bIf(Nat.beq (Nat.succ j) (nat_lit 248),
                bAnd(Nat.beq (R i) acc', strictB (Nat.succ i) (fun i' =>
                  ih (nat_lit 1) i' (nat_lit 0) (nat_lit 0))),
                strictB (Nat.succ j) (fun j' => ih (nat_lit 1) i j' acc'))),
            ih (nat_lit 1) i j acc)))))
    cs

@[expose] noncomputable def thPayK (R : Nat → Nat) (cs : List Char) : Bool :=
  thPayRun R cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def mulBlkK (X Y Z : Nat → Nat) (lo len : Nat) : Bool :=
  allBlk lo (fun i => Nat.beq (vmT Y (X i)) (Z i)) len

@[expose] noncomputable def slice (T : Nat → Nat) (k i : Nat) : Nat := T (Nat.add (Nat.mul k 248) i)

@[expose] noncomputable def wcFrom (LC : Nat → Nat) (w : List Int) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun z _ ih k => strictB (CFSG.KS.Mathieu.icode z) (fun c =>
      bAnd(bIf(Nat.beq c (nat_lit 3), Nat.beq (LC k) (nat_lit 0),
        bAnd(Nat.beq c (nat_lit 5), Nat.beq (LC k) (nat_lit 1))), ih (Nat.succ k)))) w

@[expose] noncomputable def letRow (LC A BB : Nat → Nat) (k i : Nat) : Nat :=
  nIf(Nat.beq (LC k) (nat_lit 0), A i, BB i)

end CFSG.KS.SporSch

end
