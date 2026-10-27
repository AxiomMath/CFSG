module

public import Certificates.Data.Kernel.Tower.Search14

public section

namespace Certificates.KernelTower

@[expose] def e14Tg (mul : Nat → Nat → Nat) (HL : Nat) (TG : Nat → Nat) (nq t u1 u2 v o : Nat) :
    Bool :=
  Nat.blt (Nat.land o 1023) nq && Nat.blt (Nat.shiftRight o 10) 256 &&
    Nat.beq (TG (Nat.land o 1023)) (e14Im t u1 u2 (l16 (TG (Nat.land o 1023)) 3)) &&
    Nat.beq (mul (l16 HL (Nat.shiftRight o 10)) u1) (mul u1 (l16 HL (Nat.shiftRight o 10))) &&
    Nat.beq (mul (l16 HL (Nat.shiftRight o 10)) u2) (mul u2 (l16 HL (Nat.shiftRight o 10))) &&
    Nat.beq (mul (l16 HL (Nat.shiftRight o 10)) v)
      (mul (l16 (TG (Nat.land o 1023)) 3) (l16 HL (Nat.shiftRight o 10)))

@[expose] noncomputable def e14Oc (mul : Nat → Nat → Nat) (HL GS PT f : Nat) (TG : Nat → Nat)
    (nq t u1 u2 v o : Nat) : Bool :=
  cond (Nat.beq (Nat.land o 1) 0) (e14Tg mul HL TG nq t u1 u2 v (Nat.shiftRight o 1))
    (Nat.blt (Nat.shiftRight (Nat.shiftRight o 1) 14) 4 &&
      e14Sp mul GS PT (e14Im t u1 u2 v) f (Nat.shiftRight o 1))

@[expose] noncomputable def e14VO (mul : Nat → Nat → Nat) (OT LB CZ t HL GS PT f P13 P23 : Nat)
    (TG : Nat → Nat) (nq CL3 SP u1 u2 k : Nat) : Bool :=
  !Nat.beq (pvOf16 mul OT LB CZ t u1 (l16 CL3 k)) P13 ||
    !Nat.beq (pvOf16 mul OT LB CZ t u2 (l16 CL3 k)) P23 ||
    e14Oc mul HL GS PT f TG nq t u1 u2 (l16 CL3 k) (lane SP 32 4294967295 k)

@[expose] noncomputable def e14Lvl3O (mul : Nat → Nat → Nat) (OT LB CZ t HL GS PT f R1 R2 P13 P23 : Nat)
    (TG : Nat → Nat) (nq CL3 c3 SP r2 : Nat) : Bool :=
  allB c3 (e14VO mul OT LB CZ t HL GS PT f P13 P23 TG nq CL3 SP (l16 R1 (e14P1 R2 r2)) (e14P2 R2 r2))

end Certificates.KernelTower
