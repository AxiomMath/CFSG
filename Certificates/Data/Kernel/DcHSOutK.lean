module

public import Certificates.Data.Kernel.LocalQT.PermW
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.E64F

public section

namespace CFSG.KC.DcHSOutK

open CFSG.KC.Enum

@[expose] noncomputable def fl (c i : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 c i

@[expose] noncomputable def eqF (f g : Nat → Nat) : Bool := allN 100 fun q => Nat.beq (f q) (g q)

@[expose] noncomputable def commF (f g : Nat → Nat) : Bool :=
  allN 100 fun q => Nat.beq (f (g q)) (g (f q))

@[expose] noncomputable def ltF (f : Nat → Nat) : Bool := allN 100 fun q => Nat.blt (f q) 100

@[expose] def fixF0 (f : Nat → Nat) : Bool :=
  [0, 1, 5, 21, 39, 50, 53, 61].all fun x => Nat.beq (f x) x

@[expose] def pk14 (l : List Nat) : Nat := l.foldr (fun x acc => acc * 16384 + x) 0

@[expose] noncomputable def setT (FT : Nat → Nat) (i : Nat) : List Nat :=
  [fl (FT i) 0, fl (FT i) 1, fl (FT i) 2, fl (FT i) 3, fl (FT i) 4, fl (FT i) 5, fl (FT i) 6,
    fl (FT i) 7]

@[expose] noncomputable def keyF (FT : Nat → Nat) (i : Nat) : Nat := pk14 (setT FT i)

@[expose] noncomputable def stF (A : Nat → Nat → Nat) (FT : Nat → Nat) (l i j : Nat) : Bool :=
  decide (CFSG.KC.E64F.insN ((setT FT i).map (A l)) = setT FT j)

@[expose] noncomputable def tabC (CT : Nat → Nat) (i : Nat) : List Nat :=
  (List.range 100).map (fl (CT i))

@[expose] noncomputable def keyC (CT : Nat → Nat) (i : Nat) : Nat := pk14 (tabC CT i)

@[expose] def invL (l : Nat) : Nat := if l < 2 then l + 2 else l - 2

@[expose] noncomputable def stC (A : Nat → Nat → Nat) (CT : Nat → Nat) (l i j : Nat) : Bool :=
  allN 100 fun q => Nat.beq (A l (fl (CT i) (A (invL l) q))) (fl (CT j) q)

@[expose] noncomputable def ePath (P L : Nat → Nat) (A : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, q => q
  | f + 1, k, q => if k = 0 then q else A (L k) (ePath P L A f (P k) q)

@[expose] noncomputable def ePathI (P L : Nat → Nat) (A : Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat
  | 0, _, q => q
  | f + 1, k, q => if k = 0 then q else ePathI P L A f (P k) (A (invL (L k)) q)

end CFSG.KC.DcHSOutK

end
