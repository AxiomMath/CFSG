module

public import Certificates.Data.Kernel.LocalQT.HSAutN
public import Certificates.Data.Kernel.Spor.PEnumX

public section

namespace CFSG.KS.HSL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN

@[expose] noncomputable def commK (G : Nat → Nat) (t : Nat) : Bool :=
  bIf(allN (nat_lit 6) (fun j => allN (nat_lit 2) (fun p =>
      Nat.beq (img t (img (G j) p)) (img (G j) (img t p)))),
    allN (nat_lit 6) (fun j => Nat.beq (pc t (G j)) (pc (G j) t)), false)

@[expose] noncomputable def notinK (T : Nat → Nat) (cnt x : Nat) : Bool :=
  allN cnt (fun q => bIf(Nat.beq (T q) x, false, true))

@[expose] noncomputable def sel7 (l : Nat) (f0 f1 f2 f3 f4 f5 f6 : Nat → Nat) (x : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), f0 x, nIf(Nat.beq l (nat_lit 1), f1 x,
  nIf(Nat.beq l (nat_lit 2), f2 x, nIf(Nat.beq l (nat_lit 3), f3 x,
  nIf(Nat.beq l (nat_lit 4), f4 x, nIf(Nat.beq l (nat_lit 5), f5 x, f6 x))))))

end CFSG.KS.HSL

end
