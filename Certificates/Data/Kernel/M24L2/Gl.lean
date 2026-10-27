module

public import Certificates.Data.Kernel.M24L2.Bfs
public import Certificates.Data.Kernel.M24L2.Letters
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.CGT.M24R.L2Inputs

public section

namespace CFSG.KC.M24L2

open CFSG.CGT.M24R CFSG.KC.Enum

@[expose] noncomputable def invB (m : Nat) : Bool :=
  letN (lapT m) fun T =>
    allN 15 fun x => !(Nat.beq (fldT T (Nat.add x (nat_lit 1))) (nat_lit 0))

@[expose] noncomputable def invChk (G lo n : Nat) : Bool :=
  allN n fun i => letN (Nat.add lo i) fun m =>
    bIf(invB m, !(Nat.beq (Nat.land G (Nat.shiftLeft (nat_lit 1) m)) (nat_lit 0)), true)

@[expose] noncomputable def lcX (i : Nat) : Nat := lcC (xLetters.getD i ((0 : Fin 10), true))

@[expose] noncomputable def mulX (p i : Nat) : Nat :=
  Nat.shiftRight (mulC (Nat.mul (nat_lit 16) p) (lcX i)) (nat_lit 4)

@[expose] noncomputable def treeStepL (s m p i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (addKey s m)
    (Nat.blt m (nat_lit 65536) &&
      Nat.beq (Nat.land s (Nat.shiftLeft (nat_lit 1) (Nat.add m (nat_lit 64)))) (nat_lit 0) &&
      !(Nat.beq (Nat.land s (Nat.shiftLeft (nat_lit 1) (Nat.add p (nat_lit 64)))) (nat_lit 0)) &&
      Nat.blt i (nat_lit 12) && Nat.beq (mulX p i) m)

@[expose] noncomputable def treeStep (s : Nat) (e : Nat × Nat × Nat) : Nat :=
  letN e.1 fun m => letN e.2.1 fun p => letN e.2.2 fun i => treeStepL s m p i

@[expose] noncomputable def treeK (E : List (Nat × Nat × Nat)) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun e _ ih s => letN (treeStep s e) ih) E s

@[expose] noncomputable def treeS (ES : List (List (Nat × Nat × Nat))) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun E _ ih s => letN (treeK E s) ih) ES s

end CFSG.KC.M24L2
