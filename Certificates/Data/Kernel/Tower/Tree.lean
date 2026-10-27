module

public import Certificates.Data.Kernel.Tower.W

public section

namespace Certificates.KernelTower

@[expose] def l16 (T i : Nat) : Nat := lane T 16 65535 i

@[expose] def ptPar (PT c : Nat) : Nat := Nat.land (lane PT 32 4294967295 c) 65535

@[expose] def ptGi (PT c : Nat) : Nat := Nat.land (Nat.shiftRight (lane PT 32 4294967295 c) 16) 7

@[expose] def ptDep (PT c : Nat) : Nat := Nat.shiftRight (lane PT 32 4294967295 c) 19

@[expose] noncomputable def treeB (n k : Nat) (mul : Nat → Nat → Nat) (GS PT : Nat) : Bool :=
  allB k (fun i => Nat.blt (l16 GS i) n) && allB n fun c => Nat.beq c 0 ||
    (Nat.blt (ptGi PT c) k && Nat.blt (ptPar PT c) n &&
      Nat.blt (ptDep PT (ptPar PT c)) (ptDep PT c) &&
      Nat.beq (mul (l16 GS (ptGi PT c)) (ptPar PT c)) c)

@[expose] noncomputable def recB (n k : Nat) (mul : Nat → Nat → Nat) (PT IM FT : Nat) : Bool :=
  allB k (fun i => Nat.blt (l16 IM i) n) && Nat.beq (l16 FT 0) 0 && allB n fun c => Nat.beq c 0 ||
    Nat.beq (l16 FT c) (mul (l16 IM (ptGi PT c)) (l16 FT (ptPar PT c)))

end Certificates.KernelTower
