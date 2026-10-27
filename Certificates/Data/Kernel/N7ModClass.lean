module

public import CFSG.CGT.T75M23.N7Class
public import Certificates.Data.Kernel.N6ModClass
public import CFSG.CGT.T75JM.N6Branch

public section

namespace CFSG.KernelN7

open CFSG.CGT.T75JM CFSG.CGT.T75M23 CFSG.KernelN6

@[expose] def repC7 (r : ℕ) : Cols := if r = 0 then modelX7 else transvC

@[expose] def relCB7 (X Y : Cols) : Bool :=
  eqC (compC X X) idC && !eqC X idC && eqC (powC Y 5) idC &&
    eqC (powC (compC X (compC Y (compC X (powC Y 4)))) 3) idC &&
    eqC (powC (compC (powC Y 4) X) 7) idC &&
    eqC (compC X (compC Y (compC X (compC (powC (compC Y (compC X (compC (powC Y 4)
      (compC X Y)))) 2) (compC Y (compC X (powC Y 4))))))) idC

@[expose] def equivB7 (X Y Q Qi : Cols) : Bool :=
  smallB Q && smallB Qi && eqC (compC Qi Q) idC && eqC (compC Q Qi) idC &&
    eqC (compC X Q) (compC Q modelX7) && eqC (compC Y Q) (compC Q modelY7)

@[expose] def relB7 (r n : ℕ) : Bool := relCB7 (repC7 r) (unpackC n)

@[expose] def invRecOK7 (e : ℕ) : Bool :=
  eqC (compC (unpackC (e / 65536 ^ 2 % 65536)) (unpackC (e / 65536 % 65536))) idC &&
    eqC (compC (unpackC (e / 65536 % 65536)) (unpackC (e / 65536 ^ 2 % 65536))) idC &&
    eqC (cjC (unpackC (e / 65536 % 65536)) (unpackC (e / 65536 ^ 2 % 65536)) (unpackC (e % 65536)))
      (repC7 (e / 65536 ^ 3))

@[expose] def relRecOK7 (e : ℕ) : Bool :=
  equivB7 modelX7
    (if e / 65536 ^ 3 = 0 then unpackC (e % 65536)
      else evalC modelX7 (unpackC (e % 65536)) twistWord7)
    (unpackC (e / 65536 % 65536)) (unpackC (e / 65536 ^ 2 % 65536))

@[expose] def invAll7 (L : List ℕ) : Bool :=
  eqNL ((List.range' 0 65536).filter isInvB) (L.map (· % 65536)) && L.all invRecOK7

@[expose] def relAll7 (r : ℕ) (L : List ℕ) : Bool :=
  eqNL ((List.range' 0 65536).filter (relB7 r)) (L.map (· % 65536)) && L.all relRecOK7

end CFSG.KernelN7
