module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.BfsPin

public section

namespace CFSG.KC.I242

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 3510 12 (mask 12) p q

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 3510 12 (mask 12) p

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 3510 12 (mask 12) (3510 * 12) p

@[expose] noncomputable def pm (p : Nat) : Bool := permOK 3510 12 (mask 12) (3510 * 12) p (pinv p)

@[expose] noncomputable def pid : Nat := pidn 3510 12

@[expose] noncomputable def hK (F : Nat → Nat) (i : Nat) : Nat :=
  nIf(Nat.beq i 0, pid, F (Nat.add i 2))

@[expose] noncomputable def cjI (g y : Nat) : Nat := pc (pinv g) (pc y g)

@[expose] noncomputable def cmK (g h : Nat) : Nat := pc (pc g h) (pc (pinv g) (pinv h))

@[expose] noncomputable def aK (F : Nat → Nat) (A i : Nat) : Nat := cjI (hK F i) A

@[expose] noncomputable def bK (F : Nat → Nat) (i : Nat) : Nat := cjI (hK F i) (F 1)

@[expose] noncomputable def dK (F : Nat → Nat) (A j : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod j 2) 0, cmK (aK F A (Nat.div j 2)) (bK F (Nat.div j 2)), bK F (Nat.div j 2))

@[expose] noncomputable def dIK (F : Nat → Nat) (A j : Nat) : Nat := pinv (dK F A j)

@[expose] noncomputable def cpK (p : Nat) : Bool := bAnd(cn p, bAnd(pm p, cn (pinv p)))

@[expose] noncomputable def partsK (F : Nat → Nat) (A i : Nat) : Bool :=
  bAnd(cpK (hK F i), bAnd(cpK (aK F A i), cpK (bK F i)))

@[expose] noncomputable def sigK (L : List Nat) : Nat := CFSG.KC.BfsPin.packA 12 L

@[expose] noncomputable def sigInvK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat)
    (fun _ => CFSG.KLie.CT.orN 3510 fun p => Nat.shiftLeft 120 (Nat.mul 7 p))
    (fun x _ ih v => Nat.xor (ih (Nat.succ v)) (Nat.shiftLeft (Nat.xor 120 v) (Nat.mul 7 x))) L 0

@[expose] noncomputable def sigOK (S T : Nat) : Bool :=
  allN 120 fun v => bAnd(Nat.blt (pg 12 4095 S v) 3510, Nat.beq (pg 7 127 T (pg 12 4095 S v)) v)

@[expose] noncomputable def sigInvOK (S T : Nat) : Bool :=
  allN 3510 fun p => bAnd(Nat.ble (pg 7 127 T p) 120,
    bIf(Nat.blt (pg 7 127 T p) 120, Nat.beq (pg 12 4095 S (pg 7 127 T p)) p, true))

end CFSG.KC.I242

end
