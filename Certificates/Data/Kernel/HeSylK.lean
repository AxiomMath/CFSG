module

public import Certificates.Data.Kernel.HeAutK

public section

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK
open CFSG.KLie.CT (anyN andB orB notB)

@[expose] noncomputable def restK16 (n w gX : Nat) (GX : Nat → Nat) (NX : Nat) (TX : Nat → Nat)
    (gQ : Nat) (GQ : Nat → Nat) (NQ : Nat) (TQ : Nat → Nat)
    (gE : Nat) (GE : Nat → Nat) (NE : Nat) (TE : Nat → Nat)
    (gF : Nat) (GF : Nat → Nat) (NF : Nat) (TF : Nat → Nat)
    (gU : Nat) (GU : Nat → Nat) (NU : Nat) (TU : Nat → Nat) (z r s : Nat) : Bool :=
  andB (allN gQ fun k => inL NX TX (GQ k))
  (andB (allN gE fun k => inL NX TX (GE k))
  (andB (allN gF fun k => inL NX TX (GF k))
  (andB (allN gU fun k => inL NQ TQ (GU k))
  (andB (inL NQ TQ z) (andB (inL NX TX r) (andB (inL NX TX s)
  (andB (allN gX fun k => allN gQ fun q => inL NQ TQ (conj n w (GX k) (GQ q)))
  (andB (allN gX fun k => allN gE fun q => inL NE TE (conj n w (GX k) (GE q)))
  (andB (allN gX fun k => allN gF fun q => inL NF TF (conj n w (GX k) (GF q)))
  (andB (Nat.beq (mul n w z z) (pidn n w)) (andB (notB (Nat.beq z (pidn n w)))
  (andB (allN gX fun k => comm n w z (GX k))
  (andB (allN NX fun i => strictB (TX i) fun x =>
    orB (notB (allN gX fun k => comm n w x (GX k))) (inZ n w z x))
  (andB (allN NQ fun i => strictB (TQ i) fun x => inZ n w z (mul n w x x))
  (andB (allN NQ fun i => strictB (TQ i) fun x =>
    orB (notB (allN gQ fun k => comm n w x (GQ k))) (inZ n w z x))
  (andB (anyN gQ fun a => anyN gQ fun b => notB (comm n w (GQ a) (GQ b)))
  (andB (elemAbK n w NE TE gE GE) (andB (elemAbK n w NF TF gF GF) (andB (elemAbK n w NU TU gU GU)
  (andB (anyN gE fun a => notB (inL NF TF (GE a)))
  (andB (inL NQ TQ (pw n w r 4)) (andB (inL NQ TQ (mul n w s s))
  (andB (inL NQ TQ (strictN (mul n w s r) fun t => mul n w t t))
  (andB (notB (inL NQ TQ r)) (andB (notB (inL NQ TQ (pw n w r 2)))
  (andB (notB (inL NQ TQ (pw n w r 3))) (andB (notB (inL NQ TQ s))
  (andB (notB (inL NQ TQ (mul n w s r))) (andB (notB (inL NQ TQ (mul n w s (pw n w r 2))))
    (notB (inL NQ TQ (mul n w s (pw n w r 3)))))))))))))))))))))))))))))))))

end CFSG.KC.HeAutK

end
