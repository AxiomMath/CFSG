module

public import Certificates.Data.Kernel.Sp62Pk
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KD.Sp6A2

open CFSG.KD.Sp62 CFSG.KC.Loop

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def stepH (st : Nat → Nat → Nat) (X PA PB C POS : Nat → Nat)
    (H n k hi : Nat) : Bool :=
  Nat.beq (C 0) 1 && Nat.beq (C (Nat.mul H k)) n &&
  allBelow (Nat.mul H k) hi fun i =>
    Nat.blt (Nat.div i k) (C i) && Nat.blt (Nat.div i k) n && Nat.ble (POS i) (C i) &&
    Nat.blt (POS i) n && Nat.beq (X (POS i)) (st (X (Nat.div i k)) (Nat.mod i k)) &&
    cond (Nat.beq (POS i) (C i))
      (Nat.beq (C (Nat.succ i)) (Nat.succ (C i)) && Nat.beq (PA (Nat.pred (C i))) (Nat.div i k) &&
        Nat.beq (PB (Nat.pred (C i))) (Nat.mod i k))
      (Nat.beq (C (Nat.succ i)) (C i))

@[expose] noncomputable def tableH (R : Nat → Nat) (st : Nat → Nat → Nat) (o H n hiB hiS hiT : Nat) :
    Bool :=
  buildG st (recX R o) (recF R o 0) (recF R o 1) n 2 hiB &&
    stepH st (recX R o) (recF R o 0) (recF R o 1) (recC R o) (recPOS R o) H n 2 hiS &&
    CFSG.KD.G2Three.sortK (recX R o) (recF R o 2) (recF R o 3) n hiT

@[expose] noncomputable def threeF (w : Nat) : Bool :=
  strictB w fun w => !(Nat.beq w ONE) && Nat.beq (MULF (MULF w w) w) ONE

@[expose] noncomputable def capF (R : Nat → Nat) (z hx x d : Nat) : Bool :=
  Nat.ble 2 fld(d, 0, 1048575) &&
    Nat.beq (R (Nat.sub fld(d, 0, 1048575) 2)) z && Nat.beq (R (Nat.sub fld(d, 0, 1048575) 1)) x &&
    Nat.beq (recX R fld(d, 0, 1048575) 0) ONE &&
    tableH R (rmulSt (at2 R (Nat.sub fld(d, 0, 1048575) 2))) fld(d, 0, 1048575) 168
      fld(d, 20, 1023) 6 6 6 &&
    Nat.ble 168 fld(d, 20, 1023) && Nat.ble fld(d, 20, 1023) 384 &&
    (Nat.ble 169 fld(d, 20, 1023) ||
      (Nat.blt fld(d, 30, 3) 3 && Nat.blt fld(d, 32, 255) 168 &&
        Nat.beq (recX R (R (Nat.add hx fld(d, 30, 3))) fld(d, 32, 255)) x))

@[expose] noncomputable def scanF (R8 R : Nat → Nat) (z hx o8 dk t : Nat) : Bool :=
  strictB (recX R8 o8 t) fun x =>
    bIf(threeF (MULF z x), strictB (R (Nat.add dk t)) (capF R z hx x), true)

@[expose] noncomputable def scanK (R8 R : Nat → Nat) (z hx o8 dk lo m hi : Nat) : Bool :=
  allBelow m hi fun t => scanF R8 R z hx o8 dk (Nat.add lo t)

@[expose] noncomputable def posK (R : Nat → Nat) (o n X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) n (fun t acc => nIf(Nat.beq (recX R o t) X, t, acc)) n

@[expose] noncomputable def inK (R : Nat → Nat) (o n X : Nat) : Bool :=
  strictB (posK R o n X) fun p => Nat.blt p n && Nat.beq (recX R o p) X

@[expose] noncomputable def commF (X A : Nat) : Bool := Nat.beq (MULF X A) (MULF A X)

@[expose] noncomputable def cntK (R : Nat → Nat) (o n A hi : Nat) : Nat :=
  sumBelow n hi fun t => nIf(commF (recX R o t) A, 1, 0)

@[expose] noncomputable def dFilt (A T : Nat) : Bool :=
  Nat.beq (MULF (MULF A A) A) ONE && !(Nat.beq A ONE) && Nat.beq (MULF T T) ONE &&
    !(Nat.beq T ONE) && Nat.beq (MULF (MULF T A) T) (MULF A A)

@[expose] noncomputable def listedF (R : Nat → Nat) (vb A : Nat) : Bool :=
  Nat.beq A (R vb) || Nat.beq A (R (Nat.add vb 1)) || Nat.beq A (R (Nat.add vb 2)) ||
    Nat.beq A (R (Nat.add vb 3)) || Nat.beq A (R (Nat.add vb 4)) || Nat.beq A (R (Nat.add vb 5)) ||
    Nat.beq A (R (Nat.add vb 6)) || Nat.beq A (R (Nat.add vb 7))

@[expose] noncomputable def cenK (R8 R : Nat → Nat) (vb A T : Nat) : Nat :=
  nIf(Nat.beq A (R vb) || Nat.beq A (R (Nat.add vb 1)), cntK R8 6521 108 T 2,
    nIf(Nat.beq A (R (Nat.add vb 2)) || Nat.beq A (R (Nat.add vb 3)), cntK R8 4360 2160 T 34,
      nIf(Nat.beq A (R (Nat.add vb 4)) || Nat.beq A (R (Nat.add vb 5)), cntK R 5705 648 T 11,
        nIf(Nat.beq A (R (Nat.add vb 6)) || Nat.beq A (R (Nat.add vb 7)),
          cntK R 5705 648 (MULF (MULF (R (Nat.add vb 8)) T) (R (Nat.add vb 8))) 11, 0))))

@[expose] noncomputable def dF (R8 R : Nat → Nat) (vb oK A T : Nat) : Bool :=
  bIf(dFilt A T, (inK R oK 6 A && inK R oK 6 T) ||
    (listedF R vb A && !(Nat.beq (cenK R8 R vb A T) 36)), true)

@[expose] noncomputable def dRows (R8 R : Nat → Nat) (vb oK oD lo m : Nat) : Bool :=
  allBelow m 1 fun i => strictB (recX R oD (Nat.add lo i)) fun A =>
    allBelow 36 1 fun j => strictB (recX R oD j) fun T => dF R8 R vb oK A T

end CFSG.KD.Sp6A2

end
