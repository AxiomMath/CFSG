module

public import Certificates.Data.Kernel.Misc.BfsK
public import Certificates.Data.Kernel.Mat8P

public section

namespace CFSG.KD.Sp62W

open CFSG.KD.BfsK CFSG.KC.Mat8P CFSG.KC.Loop

@[expose] def numC (c : List Nat) : Nat := code64R (c ++ [64, 128])

@[expose] def rst (R : Nat → Nat) (x s : Nat) : Nat := mulP x (R s)

@[expose] def commN (x y : Nat) : Bool := Nat.beq (mulP x y) (mulP y x)

@[expose] def gensK (R : Nat → Nat) (gens : List (List Nat)) : Bool :=
  (List.range gens.length).all fun s => Nat.beq (R s) (numC (gens.getD s []))

@[expose] noncomputable def memsK (R : Nat → Nat) (q o n : Nat) (cs : List (List Nat)) : Bool :=
  (List.range cs.length).all fun i =>
    Nat.blt (R (Nat.add q i)) n && Nat.beq (recX R o (R (Nat.add q i))) (numC (cs.getD i []))

@[expose] def cenB (G Z : List Nat) (X : Nat) : Bool := !(G.all (commN X)) || Z.contains X

@[expose] noncomputable def bBody (st : Nat → Nat → Nat) (X PA PB : Nat → Nat) (k i : Nat) : Bool :=
  Nat.ble (PA i) i && Nat.blt (PB i) k && Nat.beq (X (Nat.succ i)) (st (X (PA i)) (PB i))

@[expose] noncomputable def sBody (st : Nat → Nat → Nat) (X PA PB C POS : Nat → Nat) (n k i : Nat) :
    Bool :=
  Nat.blt (Nat.div i k) (C i) && Nat.ble (POS i) (C i) && Nat.blt (POS i) n &&
    Nat.beq (X (POS i)) (st (X (Nat.div i k)) (Nat.mod i k)) &&
    cond (Nat.beq (POS i) (C i))
      (Nat.beq (C (Nat.succ i)) (Nat.succ (C i)) && Nat.beq (PA (Nat.pred (C i))) (Nat.div i k) &&
        Nat.beq (PB (Nat.pred (C i))) (Nat.mod i k))
      (Nat.beq (C (Nat.succ i)) (C i))

@[expose] noncomputable def tBody (X SRT SRI : Nat → Nat) (n i : Nat) : Bool :=
  Nat.blt (SRT i) n && Nat.blt (SRI i) n && Nat.beq (SRI (SRT i)) i && Nat.beq (SRT (SRI i)) i &&
    cond (Nat.blt (Nat.succ i) n) (Nat.blt (X (SRT i)) (X (SRT (Nat.succ i)))) true

@[expose] noncomputable def allSl (m : Nat) (f : Nat → Bool) (j : Nat) : Bool :=
  allBelow 4096 64 fun l =>
    !(Nat.blt (Nat.add (Nat.mul j 4096) l) m) || f (Nat.add (Nat.mul j 4096) l)

@[expose] noncomputable def buildSl (R : Nat → Nat) (o n k j : Nat) : Bool :=
  allSl (Nat.sub n 1) (bBody (rst R) (recX R o) (recF R o 0) (recF R o 1) k) j

@[expose] noncomputable def stepSl (R : Nat → Nat) (o n k j : Nat) : Bool :=
  allSl (Nat.mul n k)
    (sBody (rst R) (recX R o) (recF R o 0) (recF R o 1) (recC R o k) (recPOS R o k) n k) j

@[expose] noncomputable def sortSl (R : Nat → Nat) (o n j : Nat) : Bool :=
  allSl n (tBody (recX R o) (recF R o 2) (recF R o 3) n) j

@[expose] noncomputable def cenSl (R : Nat → Nat) (o n : Nat) (G1 Z1 G2 Z2 : List Nat) (j : Nat) :
    Bool :=
  allSl n (fun t => cenB G1 Z1 (recX R o t) && cenB G2 Z2 (recX R o t)) j

end CFSG.KD.Sp62W

end
