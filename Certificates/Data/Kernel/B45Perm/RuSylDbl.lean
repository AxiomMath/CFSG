module

public import Certificates.Data.Kernel.B45Perm.RuSylSrch
public import Certificates.Data.Kernel.LocalQT.TcP
public import Certificates.Data.Kernel.PkPow

public section

namespace CFSG.KC.B45P.RuSyl

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.TC CFSG.KC.PkPow

@[expose] noncomputable def xP (TR : Nat → Nat) (o0 o1 c : Nat) : Nat :=
  pcomp 4060 12 (mask 12) (TR (Nat.add o0 (Nat.shiftRight c 3))) (TR (Nat.add o1 (Nat.land c 7)))

@[expose] noncomputable def cjP (g gi x : Nat) : Nat :=
  pcomp 4060 12 (mask 12) (pcomp 4060 12 (mask 12) g x) gi

@[expose] noncomputable def yP (TR CD : Nat → Nat) (o0 o1 : Nat) (e : Nat → Nat) (g gi : Nat) :
    Nat :=
  pcomp 4060 12 (mask 12)
    (pcomp 4060 12 (mask 12)
      (pcomp 4060 12 (mask 12) (xP TR o0 o1 (CD (e 0))) (cjP g gi (xP TR o0 o1 (CD (e 1)))))
      (xP TR o0 o1 (CD (e 2))))
    (cjP g gi (xP TR o0 o1 (CD (e 3))))

@[expose] noncomputable def dblC (TR CD : Nat → Nat) (o0 o1 idn : Nat) (G GI : List Nat)
    (e : Nat → Nat) (wd : List Int) : Bool :=
  bAnd(allN 4 (fun t => Nat.blt (e t) 495),
    wordP 4060 12 idn G GI wd fun g gi =>
      strictB (yP TR CD o0 o1 e g gi) fun Y =>
        bAnd(Nat.beq (ppw 4060 12 Y 29) idn,
          bIf(allN 4060 (fun p => Nat.beq (pg 12 (mask 12) Y p) p), false, true)))

end CFSG.KC.B45P.RuSyl

end
