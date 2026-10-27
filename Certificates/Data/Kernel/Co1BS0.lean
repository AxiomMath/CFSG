module

public import Certificates.Data.Kernel.Co1BW
public import CFSG.Certificates.Kernel.Common.StrSplit
public import CFSG.Certificates.Kernel.StrNlSp

public section

namespace CFSG.KC.Co1BS0

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KLie.CT CFSG.KC.StrNlSp

@[expose] def numsNl (cs : List Char) : List Nat :=
  (((cs.map nlSp).splitOn ' ').filter fun p => !p.isEmpty).map CFSG.KC.Str.decVal

@[expose] def goodNl (cs : List Char) : Bool := ((cs.map nlSp).splitOn ' ').all fun p => p.all Char.isDigit

@[expose] def pairsL : List Nat → List (Nat × Nat)
  | a :: b :: t => (a, b) :: pairsL t
  | _ => []

@[expose] def nSK : Nat := 19683

@[expose] noncomputable def GK (R : Nat → Nat) (j : Nat) : Nat := R ([1108, 1132, 1155].getD j 0)

@[expose] noncomputable def opsK (R : Nat → Nat) (ops : List (Nat × Nat)) (t : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun o _ ih t => andB (Nat.blt o.1 (Nat.add t 3)) (andB (Nat.blt o.2 (Nat.add t 3))
      (andB (eqK (R (Nat.add t 3)) (mulWK (R o.1) (R o.2))) (strictB (Nat.succ t) ih)))) ops t

@[expose] noncomputable def parK (R E : Nat → Nat) (par : List (Nat × Nat)) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun o _ ih i => andB (orB (Nat.beq i 0) (andB (Nat.blt o.1 i) (andB (Nat.blt o.2 3)
      (eqK (E i) (mulWK (GK R o.2) (E o.1)))))) (strictB (Nat.succ i) ih)) par i

@[expose] noncomputable def leftK (R E : Nat → Nat) (L : List Nat) (t : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun v _ ih t => andB (Nat.blt v nSK)
      (andB (eqK (mulWK (GK R (Nat.div t nSK)) (E (Nat.mod t nSK))) (E v)) (strictB (Nat.succ t) ih))) L t

@[expose] noncomputable def sortK (E S : Nat → Nat) : Bool :=
  andB (allN (Nat.sub nSK 1) fun t => Nat.blt (E (S t)) (E (S (Nat.succ t))))
    (andB (allN nSK fun t => Nat.blt (S t) nSK) (allN nSK fun i => canK (E i)))

@[expose] noncomputable def cubeK (E : Nat → Nat) (a : Nat) : Bool :=
  strictB (E a) fun x => eqK (mulWK x (mulWK x x)) oneK

@[expose] noncomputable def witAt (W : Nat → Nat) (a k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (W a) (Nat.mul (nat_lit 15) k)) (nat_lit 32767)

@[expose] noncomputable def witK (E W : Nat → Nat) (a : Nat) : Bool :=
  allN (nat_lit 81) fun k => strictB (witAt W a k) fun b =>
    andB (Nat.blt b nSK) (andB (Bool.rec (motive := fun _ => Bool) (Nat.blt (witAt W a (Nat.sub k 1)) b) true (Nat.beq k 0))
      (eqK (mulWK (E a) (E b)) (mulWK (E b) (E a))))

@[expose] noncomputable def killK (E W : Nat → Nat) (lo n : Nat) : Bool :=
  allN n fun t => strictB (Nat.add lo t) fun a =>
    orB (Nat.beq a 0) (orB (notB (cubeK E a)) (witK E W a))

end CFSG.KC.Co1BS0

end
