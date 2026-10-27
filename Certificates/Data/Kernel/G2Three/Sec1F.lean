module

public import Certificates.Data.Kernel.G2Three.Sec1T1
public import Certificates.Data.Kernel.G2Three.Sec1T3

public section

namespace CFSG.KD.G2Three.Sec1

open CFSG.KC.Loop
open CFSG.KD.G2Three.Sec1T3 (rtA)

@[expose] noncomputable def LF : Nat := Nat.sub (Nat.shiftLeft 1 784) 1

@[expose] noncomputable def SIGF : Nat := Nat.add ONEP (Nat.shiftLeft 1 784)

@[expose] noncomputable def MULF (a b : Nat) : Nat :=
  (fun f => Nat.add
      (MULP (Nat.land a LF) (nIf(Nat.beq f 1, SWP (Nat.land b LF), Nat.land b LF)))
      (Nat.shiftLeft (Nat.xor f (Nat.shiftRight b 784)) 784))
    (Nat.shiftRight a 784)

@[expose] noncomputable def closR (X G : Nat → Nat) (RT lo m hi : Nat) : Bool :=
  allBelow m hi fun j => (fun q => (fun i s => Nat.beq (X (rtA RT i s)) (MULF (X i) (G s)))
    (Nat.div q 6) (Nat.mod q 6)) (Nat.add lo j)

@[expose] noncomputable def parR (RT PA PB m hi : Nat) : Bool :=
  allBelow m hi fun i => (fun a b => bAnd(Nat.ble a i, bAnd(Nat.blt b 6,
      Nat.beq (rtA RT a b) (Nat.succ i))))
    (fld(PA, Nat.mul 7 i, 127)) (fld(PB, Nat.mul 7 i, 127))

end CFSG.KD.G2Three.Sec1

end
