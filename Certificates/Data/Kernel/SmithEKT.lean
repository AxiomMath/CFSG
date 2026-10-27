module

public import Certificates.Data.Kernel.SmithEKS
public import Certificates.Data.Kernel.SmithEKW

public section

namespace CFSG.SmithE.K

@[expose] def fld (k X : Nat) : Nat := X / 2 ^ (20 * k) % 2 ^ 20

@[expose] noncomputable def packOK (T : List (List (List (List Nat)))) : List Nat → List Nat → Bool :=
  fun P => List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun p _ ih C => tvW T p == C.map (· % 1048576) && ih (C.map (· / 1048576))) P

@[expose] noncomputable def laneK (B w : Nat) : List Nat → Nat → Bool :=
  fun P => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ _ ih V => (V % 1048576 == w ||
      (B.testBit (V % 1048576) && B.testBit (V % 1048576 ^^^ w))) && ih (V / 1048576)) P

@[expose] noncomputable def rowsT (C : List Nat) (B : Nat) (P R : List Nat) : Bool :=
  R.all fun w => laneK B w P (applyL C w)

@[expose] noncomputable def chunkT (C W P : List Nat) (a n : Nat) : Bool :=
  rowsT C (wBits W) P ((W.drop a).take n)

end CFSG.SmithE.K
