module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.W16Cls

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 128 8 (mask 8) p q

@[expose] noncomputable def pid : Nat := pidn 128 8

@[expose] noncomputable def f16 (r k : Nat) : Nat := Nat.land (Nat.shiftRight r (16 * k)) 65535

@[expose] noncomputable def letters (c : Nat) : List Nat :=
  (List.range (Nat.land c 255)).map fun t => Nat.land (Nat.shiftRight c (8 + t)) 1

@[expose] noncomputable def wordP (A : Nat → Nat) (c : Nat) : Nat :=
  (letters c).foldl (fun acc k => pc (A k) acc) pid

@[expose] noncomputable def treeK (ng N : Nat) (E P : Nat → Nat) : Bool :=
  allN N fun i => Nat.beq i 0 || (Nat.blt (f16 (P i) 0) i && Nat.blt (f16 (P i) 1) ng &&
    Nat.beq (f16 (E (f16 (P i) 0)) (f16 (P i) 1)) i)

@[expose] noncomputable def ordK (N : Nat) (T O : Nat → Nat) : Bool :=
  allN N (fun m => Nat.blt (O m) N) && allN (N - 1) fun m => Nat.blt (T (O m)) (T (O (m + 1)))

@[expose] noncomputable def orbK (A AI : Nat → Nat) (N r : Nat) (T E P O : Nat → Nat) : Bool :=
  Nat.beq (T 0) r && Nat.beq (Nat.shiftRight r 1024) 0 &&
    allN N (fun i => allN 2 fun k => Nat.blt (f16 (E i) k) N &&
      Nat.beq (pc (A k) (pc (T i) (AI k))) (T (f16 (E i) k))) &&
    treeK 2 N E P && ordK N T O

@[expose] noncomputable def sylK (G : Nat → Nat) (ng N : Nat) (L E P O : Nat → Nat) : Bool :=
  Nat.beq (L 0) pid &&
    allN N (fun i => allN ng fun k => Nat.blt (f16 (E i) k) N &&
      Nat.beq (pc (L i) (G k)) (L (f16 (E i) k))) &&
    treeK ng N E P && ordK N L O

@[expose] noncomputable def invCovK (N : Nat) (L C : Nat → Nat) (T : Nat → Nat → Nat)
    (NC : Nat → Nat) : Bool :=
  allN N fun i => Nat.beq (L i) pid || !(Nat.beq (pc (L i) (L i)) pid) ||
    (Nat.blt 0 (C i) && Nat.blt ((C i - 1) % 16) 9 && Nat.blt ((C i - 1) / 16) (NC ((C i - 1) % 16)) &&
      Nat.beq (T ((C i - 1) % 16) ((C i - 1) / 16)) (L i))

end CFSG.KC.W16Cls

end
