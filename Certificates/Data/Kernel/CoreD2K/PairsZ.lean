module

public import Certificates.Data.Kernel.CoreD2K.Pairs

public section

namespace CFSG.KS.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 Certificates.CoreD2Perm

@[expose] noncomputable def pairZK (n w p ne : Nat) (EG : Nat → Nat) (q : Nat × Nat) : Bool :=
  bIf(Nat.beq q.1 q.2, Nat.beq q.1 (nat_lit 0), pairPK n w p ne EG q)

@[expose] noncomputable def pairsZK (n w : Nat) (D : Data) (GP EG GT GTI : Nat → Nat) : Bool :=
  bAnd(allN D.pairs.length (fun i =>
      pairZK n w D.p D.eW.length EG (D.pairs.getD i (nat_lit 0, nat_lit 0))),
  bAnd(fusK n w D EG GT,
  bAnd(wordEqK n w (mask w) (pidn n w) GT GTI D.gWs.length D.wA (GP (nat_lit 0)),
    wordEqK n w (mask w) (pidn n w) GT GTI D.gWs.length D.wB (GP (nat_lit 1)))))

end CFSG.KS.CoreD2K

end
