module

public import Certificates.Data.Kernel.Misc.PermClosW

public section

namespace CFSG.KC.Misc.InvCls

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ClosW

@[expose] noncomputable def repAt (n w : Nat) (A : Nat → Nat) (nA D N : Nat) (E R : Nat → Nat)
    (RW : Nat → List Nat) (j : Nat) : Bool :=
  andB (Nat.blt (R j) N) (andB (CFSG.KC.Misc.Clos.lettersK nA (RW j))
    (CFSG.KC.LQT.P.letB (wWord n w A nA (RW j)) fun c =>
      CFSG.KC.LQT.P.letB (E (R j)) fun r =>
        Nat.beq (pcomp n w (mask w) c r) (pcomp n w (mask w) D c)))

@[expose] noncomputable def clsAt (n w one N nR : Nat) (E R CL : Nat → Nat) (k : Nat) : Bool :=
  CFSG.KC.LQT.P.letB (CL k) fun v => CFSG.KC.LQT.P.letB (E k) fun e =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (CFSG.KC.LQT.P.letB (Nat.sub v (Nat.succ n)) fun u =>
          CFSG.KC.LQT.P.letB (Nat.mod u nR) fun j => CFSG.KC.LQT.P.letB (Nat.div u nR) fun s =>
            andB (Nat.blt j nR) (andB (Nat.blt s N) (CFSG.KC.LQT.P.letB (E s) fun es =>
              Nat.beq (pcomp n w (mask w) es (E (R j))) (pcomp n w (mask w) e es))))
        (notB (Nat.beq (pg w (mask w) e (pg w (mask w) e (Nat.sub v (nat_lit 1))))
          (Nat.sub v (nat_lit 1))))
        (Nat.ble v n))
      (Nat.beq e one)
      (Nat.beq v (nat_lit 0))

end CFSG.KC.Misc.InvCls

end
