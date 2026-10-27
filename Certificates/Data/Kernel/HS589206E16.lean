module

public import Certificates.Data.Kernel.DcHSOutK

public section

namespace CFSG.KC.HS589206E16

open CFSG.KC.DcHSOutK CFSG.KC.Enum

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool := !allN n fun i => !f i

@[expose] noncomputable def isInvF (f : Nat → Nat) : Bool :=
  eqF (fun q => f (f q)) (fun q => q) && !eqF f (fun q => q)

@[expose] noncomputable def invsK (F : Nat → Nat → Nat) (N : Nat) (ix : Nat → Nat) (n : Nat) :
    Bool :=
  allN n (fun i => Nat.blt (ix i) N && isInvF (F (ix i))) &&
    allN (Nat.sub n 1) (fun i => Nat.blt (ix i) (ix (Nat.add i 1))) &&
    allN N (fun k => !isInvF (F k) || anyN n fun i => Nat.beq (ix i) k)

@[expose] noncomputable def pe (PT : Nat → Nat) (a b : Nat) : Nat := fl (PT a) b

@[expose] noncomputable def cm (PT : Nat → Nat) (a b : Nat) : Bool :=
  Nat.blt 0 (pe PT a b) && Nat.blt (pe PT a b) 128

@[expose] noncomputable def mul (PT : Nat → Nat) (a b : Nat) : Nat := Nat.sub (pe PT a b) 1

@[expose] noncomputable def pairC (I : Nat → Nat → Nat) (n a b c : Nat) : Bool :=
  cond (Nat.beq c 0) (Nat.beq a b)
    (cond (Nat.blt c 128)
      (!Nat.beq a b && Nat.blt (Nat.sub c 1) n &&
        eqF (fun q => I a (I b q)) (I (Nat.sub c 1)) &&
        eqF (fun q => I b (I a q)) (I (Nat.sub c 1)))
      (Nat.blt (Nat.sub c 128) 100 &&
        !Nat.beq (I a (I b (Nat.sub c 128))) (I b (I a (Nat.sub c 128)))))

@[expose] noncomputable def pairT (I : Nat → Nat → Nat) (PT : Nat → Nat) (n a b : Nat) : Bool :=
  pairC I n a b (pe PT a b)

@[expose] noncomputable def pairsK (I : Nat → Nat → Nat) (PT : Nat → Nat) (n lo len : Nat) :
    Bool :=
  allBlk lo (fun a => allN n (fun b => pairT I PT n a b)) len

@[expose] noncomputable def qEl (PT : Nat → Nat) (i j k l : Nat) : List Nat :=
  [i, j, k, l, mul PT i j, mul PT i k, mul PT i l, mul PT j k, mul PT j l, mul PT k l,
    mul PT (mul PT i j) k, mul PT (mul PT i j) l, mul PT (mul PT i k) l, mul PT (mul PT j k) l,
    mul PT (mul PT (mul PT i j) k) l]

@[expose] noncomputable def qDef (PT : Nat → Nat) (i j k l : Nat) : Bool :=
  cm PT (mul PT i j) k && cm PT (mul PT i j) l && cm PT (mul PT i k) l && cm PT (mul PT j k) l &&
    cm PT (mul PT (mul PT i j) k) l

@[expose] def maskS (xs : List Nat) : Nat :=
  xs.foldr (fun x acc => Nat.add (Nat.shiftLeft 1 x) acc) 0

@[expose] def maskO (xs : List Nat) : Nat :=
  xs.foldr (fun x acc => Nat.lor (Nat.shiftLeft 1 x) acc) 0

@[expose] noncomputable def maskT (MK : Nat → Nat) (nm : Nat) (xs : List Nat) : Bool :=
  !Nat.beq (maskS xs) (maskO xs) || anyN nm fun t => Nat.beq (MK t) (maskS xs)

@[expose] noncomputable def quadT (PT MK : Nat → Nat) (nm i j k l : Nat) : Bool :=
  !qDef PT i j k l || maskT MK nm (qEl PT i j k l)

@[expose] noncomputable def quadBlk (PT MK : Nat → Nat) (nm n lo len : Nat) : Bool :=
  allBlk lo (fun i => allBlk (Nat.add i 1) (fun j => !cm PT i j ||
    allBlk (Nat.add j 1) (fun k => !(cm PT i k && cm PT j k) ||
      allBlk (Nat.add k 1) (fun l => !(cm PT i l && cm PT j l && cm PT k l) ||
        quadT PT MK nm i j k l) (Nat.sub (Nat.sub n 1) k))
      (Nat.sub (Nat.sub n 1) j))
    (Nat.sub (Nat.sub n 1) i)) len

end CFSG.KC.HS589206E16

end
