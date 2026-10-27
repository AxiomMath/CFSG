module

public import CFSG.Certificates.Kernel.Lie.CT.Core
public import Certificates.Data.Kernel.MonsterB.FischerK
public import CFSG.Monster.B.TwoA.Fischer.GramDataLit

public section

namespace CFSG.KC.Rem3069

open CFSG.KLie.CT CFSG.KC.FischerK CFSG.Monster.B.TwoA.Fischer

@[expose] def remN : Nat := 694980

@[expose] def remSeedN : Nat := 16058837527637121392057

@[expose] noncomputable def fourColL (g : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    (Bool.rec (motive := fun _ => List Nat) GramLit.fourCol0 GramLit.fourCol1 (Nat.beq g 1))
    (Bool.rec (motive := fun _ => List Nat) GramLit.fourCol2 GramLit.fourCol3 (Nat.beq g 3))
    (Nat.ble 2 g)

@[expose] def vecOf (r : Nat) : Nat := Nat.land r 1208925819614629174706175

@[expose] def parOf (r : Nat) : Nat := Nat.land (Nat.shiftRight r 80) 16777215

@[expose] def genOf (r : Nat) : Nat := Nat.land (Nat.shiftRight r 104) 3

@[expose] def depOf (r : Nat) : Nat := Nat.shiftRight r 106

@[expose] noncomputable def recAt (R : Nat → Nat) (i : Nat) : Nat :=
  fget (R (Nat.div i 1000)) (Nat.mod i 1000) 112

@[expose] noncomputable def edgeOK (d g v q : Nat) : Bool :=
  Nat.beq (Nat.succ (depOf q)) d && Nat.beq v (vecMulL (fourColL g) (vecOf q))

@[expose] noncomputable def recOKr (R : Nat → Nat) (i r : Nat) : Bool :=
  Nat.blt (vecOf r) 302231454903657293676544 &&
    (Nat.beq (Nat.succ i) remN || Nat.blt (vecOf r) (vecOf (recAt R (Nat.succ i)))) &&
    Bool.rec (motive := fun _ => Bool)
      (Nat.blt (parOf r) remN && edgeOK (depOf r) (genOf r) (vecOf r) (recAt R (parOf r)))
      (Nat.beq (vecOf r) remSeedN) (Nat.beq (depOf r) 0)

@[expose] noncomputable def recOK (R : Nat → Nat) (i : Nat) : Bool := recOKr R i (recAt R i)

@[expose] noncomputable def allFrom (f : Nat → Bool) (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => f (Nat.add lo k) && ih) n

@[expose] noncomputable def cntOf (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.sub remN (Nat.mul c 1000)) 1000
    (Nat.ble (Nat.mul (Nat.succ c) 1000) remN)

@[expose] noncomputable def chunkOK (R : Nat → Nat) (c : Nat) : Bool :=
  allFrom (recOK R) (Nat.mul c 1000) (cntOf c)

end CFSG.KC.Rem3069

end
