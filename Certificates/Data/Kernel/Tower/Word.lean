module

public import Certificates.Data.Kernel.Tower.T2

public section

namespace Certificates.KernelTower

@[expose] noncomputable def wevN (mul : Nat → Nat → Nat) (G n w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih w => Bool.rec (motive := fun _ => Nat)
      (mul (l16 G (Nat.land (Nat.sub (Nat.land w 7) 1) 3)) (ih (Nat.shiftRight w 3))) 0
      (Nat.beq (Nat.land w 7) 0)) n w

@[expose] noncomputable def wev (mul : Nat → Nat → Nat) (G w : Nat) : Nat := wevN mul G 21 w

@[expose] def l64 (T i : Nat) : Nat := lane T 64 18446744073709551615 i

@[expose] noncomputable def tgtOK (mul : Nat → Nat → Nat) (GS IMW b G U W X H g2 : Nat) : Bool :=
  allB 4 (fun i => Nat.blt (l16 G i) 16384 && Nat.blt (l16 U i) 16384) &&
    allB 4 (fun i => Nat.beq (wev mul G (l64 W i)) (Nat.mul 2 (l16 GS i)) &&
      Nat.beq (wev mul U (l64 W i))
        (Nat.xor (l16 IMW i) (Nat.mul 2 (xbit X (Nat.mul 2 (l16 GS i)))))) &&
    Nat.beq (wev mul G (l64 W 4)) 1 && Nat.beq (wev mul U (l64 W 4)) (Nat.xor b (Nat.mul 2 (xbit X 1))) &&
    Nat.blt H 16384 && Nat.blt g2 16384 && Nat.beq (mul H g2) 0

end Certificates.KernelTower
