module

public import Certificates.Data.Kernel.QuatPack

public section

namespace CFSG.KC.QuatK

open CFSG.KC.Enum CFSG.KS

variable (n w : Nat)

@[expose] noncomputable def ap2 (t s x : Nat) : Nat := pg w (mask w) t (pg w (mask w) s x)

@[expose] noncomputable def twP (t s a b : Nat) : Bool :=
  allN n fun x => Nat.beq (ap2 w t s (pg w (mask w) a x)) (pg w (mask w) b (ap2 w t s x))

@[expose] noncomputable def sqP (t s : Nat) : Bool :=
  allN n fun x => Nat.beq (ap2 w t s (ap2 w t s x)) x

@[expose] noncomputable def spRefK (t s e r u v u' v' : Nat) (L : List Nat) : Bool :=
  !twP n w t s u u || !twP n w t s v v || !sqP n w t s ||
    L.all (fun b => !twP n w t s u' b) || L.all (fun b => !twP n w t s v' b) ||
    L.any fun b => !Nat.beq b e && !Nat.beq b r && twP n w t s b b

@[expose] noncomputable def spScanK (T : Nat → Nat) (N s e r u v u' v' : Nat) (L : List Nat) :
    Bool :=
  allN N fun i => strictB (T i) fun t => spRefK n w t s e r u v u' v' L

end CFSG.KC.QuatK

end
