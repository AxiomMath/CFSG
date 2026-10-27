module

public import Certificates.Data.Kernel.Fendel

public section

namespace CFSG.KC.Co3Bfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel

@[expose] noncomputable def pt (X i : Nat) : Nat := pg 9 (mask 9) X i

@[expose] noncomputable def keyR (X : Nat) : Nat := Nat.add (Nat.mul (pt X 0) 276) (pt X 1)

@[expose] noncomputable def key4 (X : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (pt X 0) 276) (pt X 1)) 276) (pt X 2)) 276)
    (pt X 3)

@[expose] noncomputable def allFrom (a len : Nat) (f : Nat → Bool) : Bool :=
  allN len (fun d => strictB (Nat.add a d) f)

@[expose] noncomputable def stepR (GP E P L : Nat → Nat) (k : Nat) : Bool :=
  bAnd(Nat.blt (P k) k, bAnd(Nat.blt (L k) 3, prodOK (E (P k)) (GP (L k)) (E k)))

@[expose] noncomputable def stepC (GP GIP E P L : Nat → Nat) (k : Nat) : Bool :=
  bAnd(Nat.blt (P k) k, bAnd(Nat.blt (L k) 7,
  strictB (pc (E (P k)) (GP (L k))) (fun X =>
    bAnd(prodOK (E (P k)) (GP (L k)) X, prodOK (GIP (L k)) X (E k)))))

@[expose] noncomputable def lexOK (P L : Nat → Nat) (k : Nat) : Bool :=
  lexLtK (P k) (L k) (P (Nat.succ k)) (L (Nat.succ k))

@[expose] noncomputable def cloR (GP E P L K : Nat → Nat) (c q i : Nat) : Bool :=
  strictB (K (Nat.add (Nat.mul 3 q) i)) (fun k => bAnd(Nat.blt k c,
  bAnd(Nat.beq (keyR (E k)) (Nat.add (Nat.mul (pt (E q) (pt (GP i) 0)) 276)
      (pt (E q) (pt (GP i) 1))),
    bIf(Nat.beq k 0, true, bIf(lexLtK q i (P k) (L k), false, true)))))

@[expose] noncomputable def cpt (GP GIP E : Nat → Nat) (q i p : Nat) : Nat :=
  pt (GIP i) (pt (E q) (pt (GP i) p))

@[expose] noncomputable def cloC (GP GIP E P L K : Nat → Nat) (c q i : Nat) : Bool :=
  strictB (K (Nat.add (Nat.mul 7 q) i)) (fun k => bAnd(Nat.blt k c,
  bAnd(Nat.beq (key4 (E k)) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul
      (cpt GP GIP E q i 0) 276) (cpt GP GIP E q i 1)) 276) (cpt GP GIP E q i 2)) 276)
      (cpt GP GIP E q i 3)),
    bIf(Nat.beq k 0, true, bIf(lexLtK q i (P k) (L k), false, true)))))

@[expose] noncomputable def sortK (key : Nat → Nat) (E S SI : Nat → Nat) (c m : Nat) : Bool :=
  bAnd(Nat.blt (S m) c, bAnd(Nat.blt (SI m) c, bAnd(Nat.beq (S (SI m)) m,
    bIf(Nat.blt (Nat.succ m) c, Nat.blt (key (E (S m))) (key (E (S (Nat.succ m)))), true))))

@[expose] noncomputable def canonE (E : Nat → Nat) (k : Nat) : Bool :=
  canonK 276 9 (mask 9) (Nat.mul 276 9) (E k)

end CFSG.KC.Co3Bfs

end
