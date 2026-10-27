module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.L34Inv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (andB orB notB anyN)

@[expose] noncomputable def centSl (n w : Nat) (T : Nat → Nat) (r L : Nat) (CC : Nat → Nat)
    (s : Nat) : Bool :=
  Nat.beq (Nat.add (CC s) (CFSG.KC.HeAutK.cntR (fun i => commPt n w (T i) r) (Nat.mul L s) L))
    (CC (Nat.succ s))

@[expose] noncomputable def centList (n w N : Nat) (T : Nat → Nat) (r m : Nat) (I CT : Nat → Nat) :
    Bool :=
  allN m fun k => strictB (I k) fun j =>
    andB (Nat.blt j N) (andB (orB (Nat.beq (Nat.succ k) m) (Nat.blt j (I (Nat.succ k))))
      (andB (commPt n w (T j) r) (Nat.beq (CT k) (T j))))

@[expose] noncomputable def memK (N : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  anyN N fun i => Nat.beq (T i) x

@[expose] noncomputable def ord3K (n w e y : Nat) : Bool :=
  andB (notB (Nat.beq y e))
    (Nat.beq (pcomp n w (mask w) y (pcomp n w (mask w) y (pcomp n w (mask w) y e))) e)

@[expose] noncomputable def invNeK (n w e r x : Nat) : Bool :=
  andB (Nat.beq (pcomp n w (mask w) x x) e) (andB (notB (Nat.beq x e)) (notB (Nat.beq x r)))

@[expose] noncomputable def hl34K (n w m : Nat) (CT : Nat → Nat) (r N₂ : Nat) (O₂ : Nat → Nat)
    (N₄ : Nat) (O₄ : Nat → Nat) : Bool :=
  strictB (pidn n w) fun e => allN m fun k => strictB (CT k) fun x =>
    orB (notB (andB (invNeK n w e r x) (anyN m fun j => strictB (CT j) fun y =>
        andB (ord3K n w e y) (Nat.beq (pcomp n w (mask w) y x) (pcomp n w (mask w) x y)))))
      (strictB (pcomp n w (mask w) r x) fun rx =>
        orB (andB (memK N₂ O₂ x) (memK N₄ O₄ rx)) (andB (memK N₄ O₄ x) (memK N₂ O₂ rx)))

@[expose] noncomputable def hfi34K (n w m : Nat) (CT : Nat → Nat) (r N₃ : Nat) (O₃ : Nat → Nat) :
    Bool :=
  strictB (pidn n w) fun e => allN m fun k => strictB (CT k) fun x =>
    orB (notB (invNeK n w e r x))
      (orB (notB (memK N₃ O₃ x)) (notB (memK N₃ O₃ (pcomp n w (mask w) r x))))

end CFSG.KC.L34Inv

end
