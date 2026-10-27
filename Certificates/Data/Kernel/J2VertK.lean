module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.MonsterB.Co2Perm
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.J2VertK

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def treeK (n w ng : Nat) (G T : Nat → Nat) (pl : List (Nat × Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun pr _ ih k => bAnd(Nat.ble pr.1 k, bAnd(Nat.blt pr.2 ng,
      bAnd(Nat.beq (T (Nat.succ k)) (pcomp n w (mask w) (T pr.1) (G pr.2)), ih (Nat.succ k))))) pl

@[expose] noncomputable def sortK (N : Nat) (T : Nat → Nat) (S ws : Nat) : Bool :=
  bAnd(CFSG.KC.Co2Mem.permK N ws S, allN (Nat.sub N 1) (fun i =>
    Nat.blt (T (pg ws (mask ws) S i)) (T (pg ws (mask ws) S (Nat.succ i)))))

@[expose] noncomputable def relK (n w : Nat) (G GI : Nat → Nat) (r : List (Fin 8 × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun p _ acc => pcomp n w (mask w) (nIf(p.2, G p.1.val, GI p.1.val)) acc) r

@[expose] noncomputable def evalK (n w : Nat) (B : Nat → Nat) (wd : List (Fin 3)) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w) (fun k _ acc => pcomp n w (mask w) (B k.val) acc) wd

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  bIf(allN n (fun i => bIf(f i, false, true)), false, true)

@[expose] noncomputable def countN (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i s => nIf(f i, Nat.succ s, s)) n

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) l

end CFSG.KC.J2VertK

end
