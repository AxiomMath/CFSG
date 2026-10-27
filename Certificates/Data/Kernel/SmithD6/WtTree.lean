module

public import Certificates.Data.Kernel.SmithD6.WtCheck
public import Certificates.Data.Kernel.SmithD6.T3cData
public import Certificates.Data.Kernel.PkTree

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree

@[expose] noncomputable def wtParOK (D d f : Nat) : Bool :=
  bAnd(Nat.blt 0 f, bAnd(Nat.blt 0 (pkGet D 6 (Nat.pred f)), Nat.blt (pkGet D 6 (Nat.pred f)) d))

@[expose] noncomputable def wtRecGo (D s i d g : Nat) : Bool :=
  bAnd(Nat.blt 0 d, bIf(Nat.beq d 1, Nat.beq i 0,
    bAnd(Nat.blt g 13, wtParOK D d (KT.find (liftT (JT.gensT.getD g []) s) wt64Tree))))

@[expose] noncomputable def wtRecOK (D G s i : Nat) : Bool :=
  wtRecGo D s i (pkGet D 6 i) (pkGet G 4 i)

@[expose] noncomputable def wtTreeGo (D G : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun s _ ih i => bAnd(wtRecOK D G s i, ih (Nat.succ i))) l

@[expose] noncomputable def d6WtTreeOK (c : Nat) : Bool :=
  wtTreeGo JG.wtD JG.wtG (nthC J.wt64C c) (Nat.mul 2048 c)

end CFSG.KD.SmithD6

end
