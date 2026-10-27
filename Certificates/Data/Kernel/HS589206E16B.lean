module

public import Certificates.Data.Kernel.HS589206E16

public section

namespace CFSG.KC.HS589206E16

open CFSG.KC.DcHSOutK CFSG.KC.Enum

@[expose] def bit (m i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

@[expose] noncomputable def fixM (I : Nat → Nat → Nat) (n m q : Nat) : Bool :=
  allN n fun i => !bit m i || Nat.beq (I i q) q

@[expose] noncomputable def goodK (I : Nat → Nat → Nat) (n m : Nat) (l : List Nat) : Bool :=
  allN 100 fun q => Bool.beq (fixM I n m q) (l.any fun x => Nat.beq x q)

@[expose] noncomputable def inBlk (R : Nat → Nat) (q : Nat) : Bool := anyN 8 fun s => Nat.beq (R s) q

@[expose] noncomputable def blkT (I : Nat → Nat → Nat) (n m : Nat) (R : Nat → Nat) (b : Nat) :
    Bool :=
  Nat.blt (R (Nat.mul 2 b)) 100 && Nat.blt (R (Nat.add (Nat.mul 2 b) 1)) 100 &&
    allN n (fun i => !bit m i || Nat.beq (I i (R (Nat.mul 2 b))) (R (Nat.mul 2 b)) ||
      Nat.beq (I i (R (Nat.mul 2 b))) (R (Nat.add (Nat.mul 2 b) 1))) &&
    anyN n (fun i => bit m i && Nat.beq (I i (R (Nat.mul 2 b))) (R (Nat.add (Nat.mul 2 b) 1)))

@[expose] noncomputable def outT (I : Nat → Nat → Nat) (n m : Nat) (R : Nat → Nat) (q : Nat) :
    Bool :=
  inBlk R q ||
    (Nat.blt (R (Nat.add 8 (Nat.mul 2 q))) n && Nat.blt (R (Nat.add 9 (Nat.mul 2 q))) n &&
      bit m (R (Nat.add 8 (Nat.mul 2 q))) && bit m (R (Nat.add 9 (Nat.mul 2 q))) &&
      !Nat.beq (I (R (Nat.add 8 (Nat.mul 2 q))) q) q &&
      !Nat.beq (I (R (Nat.add 9 (Nat.mul 2 q))) q) q &&
      !Nat.beq (I (R (Nat.add 8 (Nat.mul 2 q))) q) (I (R (Nat.add 9 (Nat.mul 2 q))) q))

@[expose] noncomputable def badK (I : Nat → Nat → Nat) (n m : Nat) (R : Nat → Nat) : Bool :=
  allN 8 (fun s => allN 8 fun s' => Nat.beq s s' || !Nat.beq (R s) (R s')) &&
    allN 4 (blkT I n m R) && allN 100 (outT I n m R)

@[expose] def wdR (R : Nat → Nat) : List Nat := (List.range (R 1)).map fun j => R (j + 2)

@[expose] noncomputable def eT (I A : Nat → Nat → Nat) (F0 : List Nat) (n m : Nat) (R : Nat → Nat) :
    Bool :=
  cond (Nat.beq (R 0) 0)
    (allN (R 1) (fun j => Nat.blt (R (Nat.add j 2)) 4) &&
      goodK I n m (F0.map (CFSG.KC.E64F.wordF A (wdR R))))
    (badK I n m fun s => R (Nat.add s 1))

@[expose] noncomputable def cntF (f : Nat → Nat) : Nat :=
  foldN 100 (fun q s => cond (Nat.beq (f q) q) (Nat.succ s) s) 0

@[expose] noncomputable def fix5K (F : Nat → Nat → Nat) (N b : Nat) : Bool :=
  allN N fun k => eqF (F k) (fun q => q) || Nat.ble (cntF (F k)) b

end CFSG.KC.HS589206E16

end
