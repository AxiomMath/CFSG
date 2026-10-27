module

public import Certificates.Kernel.B433Alt.Data.St
public import Certificates.Data.Kernel.B433Alt.Struct
public import CFSG.Certificates.Kernel.YModel.Texts.YM432P

public section

namespace CFSG.KD.B4A

open CFSG.KC.B4A CFSG.KC.Y333

@[expose] noncomputable def ptsOK (f : Nat → Bool) (a n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (Bool.rec (motive := fun _ => Bool) true (f (Nat.add a i))
      (Nat.blt (Nat.add a i) (nat_lit 31671)))) n

@[expose] noncomputable def letChk (k : Nat) : Bool :=
  sB (LP (Nat.div k 32)) fun P => sB (CFSG.KD.YM432P.F (Nat.div k 32)) fun F =>
    andB (Nat.blt k (nat_lit 320))
      (ptsOK (fun x => Nat.beq (pget P x) (CFSG.KC.YModel.fieldAt (nat_lit 32) F x))
        (Nat.mul (nat_lit 1000) (Nat.mod k 32)) (nat_lit 1000))

@[expose] noncomputable def pairChk (k : Nat) : Bool :=
  sB (Nat.div k 8) fun t =>
  sB (LP (Nat.add (nat_lit 10) t)) fun R => sB (LP (Nat.div t 10)) fun P => sB (LP (Nat.mod t 10)) fun Q =>
    andB (Nat.blt k (nat_lit 800))
      (ptsOK (fun x => Nat.beq (pget R x) (pget P (pget Q x))) (Nat.mul (nat_lit 4000) (Nat.mod k 8))
        (nat_lit 4000))

end CFSG.KD.B4A

end
