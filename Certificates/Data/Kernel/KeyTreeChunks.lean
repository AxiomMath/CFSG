module

public import Certificates.Data.Kernel.KeyTree

public section

namespace CFSG.KC.KeyTree

@[expose] noncomputable def KT.size (t : KT) : Nat :=
  KT.rec (motive := fun _ => Nat) 0 (fun _ _ _ _ il ir => Nat.succ (Nat.add il ir)) t

@[expose] noncomputable def lenC (cs : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) cs

@[expose] noncomputable def nthC (cs : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun ch _ ih c => Nat.rec (motive := fun _ => List Nat) ch (fun c' _ => ih c') c) cs

@[expose] noncomputable def isConsL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun _ _ _ => true) l

@[expose] noncomputable def headL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun k _ _ => k) l

@[expose] noncomputable def strictKB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def chunkGo (t : KT) (hasNx : Bool) (nx e : Nat) (l : List Nat) :
    Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun pos lo => bAnd(Nat.beq pos e, bIf(hasNx, Nat.ble lo nx, true)))
    (fun k _ ih pos lo => bAnd(Nat.ble lo k,
      bAnd(Nat.beq (KT.find k t) (Nat.succ pos),
        strictKB (Nat.succ pos) (fun p => ih p (Nat.succ k))))) l

@[expose] noncomputable def KT.chunkOK (t : KT) (sz N : Nat) (cs : List (List Nat)) (c : Nat) :
    Bool :=
  chunkGo t (isConsL (nthC cs (Nat.succ c))) (headL (nthC cs (Nat.succ c)))
    (nIf(Nat.blt (Nat.succ c) (lenC cs), Nat.mul sz (Nat.succ c), N)) (nthC cs c) (Nat.mul sz c) 0

@[expose] noncomputable def KT.idx (n x : Nat) (t : KT) : Nat :=
  nIf(Nat.beq (KT.find x t) 0, n, Nat.pred (KT.find x t))

end CFSG.KC.KeyTree

end
