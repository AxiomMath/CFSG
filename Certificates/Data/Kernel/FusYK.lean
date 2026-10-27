module

public import Certificates.Data.Kernel.Q47K

public section

namespace CFSG.KC.FusYK

open CFSG.KC.Enum CFSG.KS CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.Q47K
open CFSG.KLie.CT (anyN sumN andB orB notB)

@[expose] noncomputable def tabK (n w : Nat) (REP : Nat → Nat) (z : Nat) (L : List Nat) : Nat :=
  sumN 64 fun v => Nat.mul (bn (CFSG.KLie.CT.orB (memK L (REP v)) (memK L (mul n w (REP v) z)))) (Nat.shiftLeft 1 v)

@[expose] noncomputable def cosetK (n w : Nat) (LQ : List Nat) (e : Nat) (L : List Nat) : Bool :=
  LQ.all fun q => strictB (mul n w e q) fun x =>
    CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (Nat.beq (mul n w x x) (pidn n w))) (memK L x)

@[expose] noncomputable def orbitK (form : Array Nat) (K : List Nat) (tab : Nat) : Bool :=
  allN 64 fun v => CFSG.KLie.CT.orB (Nat.beq v 0) (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (Nat.beq form[v]! 0))
    (K.any fun k => bitK tab (pg 7 (mask 7) k v)))

@[expose] noncomputable def invK (K : List Nat) (t : Nat) (W : List Nat) : Bool :=
  (List.range K.length).all fun i => strictB (K.getD i 0) fun x =>
    CFSG.KLie.CT.orB (Nat.beq x (pidn 64 7)) (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (Nat.beq (mul 64 7 x x) (pidn 64 7)))
      (CFSG.KLie.CT.andB (Nat.blt (W.getD i 0) K.length) (Nat.beq (conj 64 7 (K.getD (W.getD i 0) 0) x) t)))

end CFSG.KC.FusYK

end
