module

public import Certificates.Data.Kernel.Tower.Search14

public section

namespace Certificates.KernelTower

@[expose] noncomputable def ninvC (n : Nat) (mul : Nat → Nat → Nat) (OT r : Nat) : Nat :=
  cntB n fun c => Nat.beq (oe OT c) 1 && Nat.beq (mul c r) (mul r c)

@[expose] noncomputable def pcB (n : Nat) (mul : Nat → Nat → Nat) (OT LB RP CZ nl t x0 : Nat) : Bool :=
  allB nl fun l =>
    !(Nat.beq (oe OT (l16 RP l)) 1 && Nat.beq (lane CZ 15 32767 l) 64 &&
        Nat.beq (ninvC n mul OT (l16 RP l)) 87) ||
      Nat.beq l (lbL LB t) || Nat.beq l (lbL LB x0)

@[expose] noncomputable def chiB (n : Nat) (mul : Nat → Nat → Nat) (GS XT t x0 : Nat) : Bool :=
  Nat.beq (bit XT 0) 0 && Nat.beq (bit XT t) 1 && Nat.beq (bit XT x0) 1 &&
    allB n fun c => allB 4 fun s =>
      Nat.beq (bit XT (mul (l16 GS s) c)) (Nat.xor (bit XT (l16 GS s)) (bit XT c))

end Certificates.KernelTower
