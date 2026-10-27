module

public import Certificates.Data.Kernel.SmithEKS

public section

namespace CFSG.SmithE.K

@[expose] noncomputable def cwK (B : Nat) : List Nat → List (List Nat) → Bool :=
  fun E => List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun Cs => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Cs)
    (fun e _ ih Cs => List.rec (motive := fun _ => Bool) false
      (fun c Cs' _ => Nat.blt e 2048 &&
        Nat.beq (Nat.land (Nat.shiftRight B (Nat.xor (applyL c e) e)) 1) 1 && ih Cs') Cs) E

end CFSG.SmithE.K
