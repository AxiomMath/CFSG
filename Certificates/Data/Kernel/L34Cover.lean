module

public import Certificates.Data.Kernel.L34Inv

public section

namespace CFSG.KC.L34Inv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (fget andB orB notB)

@[expose] noncomputable def covSl (n w : Nat) (T : Nat → Nat) (OT : Nat → Nat → Nat)
    (ON : Nat → Nat) (no : Nat) (W : Nat → Nat) (L s : Nat) : Bool :=
  strictB (pidn n w) fun e => allN L fun i => strictB (Nat.add (Nat.mul L s) i) fun k =>
    strictB (T k) fun x =>
      orB (Nat.beq x e) (orB (notB (Nat.beq (pcomp n w (mask w) x x) e))
        (strictB (fget (W (Nat.shiftRight k (nat_lit 4))) (Nat.land k (nat_lit 15)) (nat_lit 11))
          fun v => strictB (Nat.shiftRight v (nat_lit 10)) fun o =>
            strictB (Nat.land v (nat_lit 1023)) fun j =>
              andB (Nat.blt o no) (andB (Nat.blt j (ON o)) (Nat.beq (OT o j) x))))

@[expose] noncomputable def conjWitK (n w N : Nat) (T : Nat → Nat) (m : Nat) (CT : Nat → Nat)
    (a NA : Nat) (OA H : Nat → Nat) : Bool :=
  strictB (pidn n w) fun e => allN m fun k => strictB (CT k) fun x =>
    orB (notB (andB (invNeK n w e a x)
        (andB (memK NA OA x) (memK NA OA (pcomp n w (mask w) a x)))))
      (strictB (H k) fun j => andB (Nat.blt j N) (strictB (T j) fun h =>
        andB (Nat.beq (pcomp n w (mask w) h a) (pcomp n w (mask w) x h))
          (Nat.beq (pcomp n w (mask w) h x)
            (pcomp n w (mask w) (pcomp n w (mask w) a x) h))))

end CFSG.KC.L34Inv

end
