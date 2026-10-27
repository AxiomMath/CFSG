module

public import Certificates.Data.Kernel.Spor.ONK

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum CFSG.KS.ON

@[expose] noncomputable def tabAt (F : Nat → Nat) (k p : Nat) : Nat :=
  fld(F (Nat.add (Nat.mul (nat_lit 511) k) (Nat.div p (nat_lit 52))),
    Nat.mul (nat_lit 16) (Nat.mod p (nat_lit 52)), nat_lit 65535)

@[expose] noncomputable def keyChk (KT : Nat → Nat) (L : List Nat) (T : Nat → Nat) (p : Nat) :
    Bool :=
  strictB (T p) fun q => bAnd(Nat.blt q (nat_lit 26572),
    strictB (mv L (key KT p)) fun w => strictB (key KT q) fun u =>
      bIf(Nat.beq w u, true, Nat.beq w (vneg u)))

@[expose] noncomputable def keyChunk (KT : Nat → Nat) (L : List Nat) (T : Nat → Nat) (c : Nat) :
    Bool :=
  allBlk (Nat.mul (nat_lit 256) c)
    (fun p => bIf(Nat.blt p (nat_lit 26572), keyChk KT L T p, true)) (nat_lit 256)

@[expose] noncomputable def canonPk (X : Nat) : Nat := nIf(Nat.blt X (vneg X), X, vneg X)

@[expose] noncomputable def wf84 (X : Nat) : Bool :=
  strictB (vP X) fun p => strictB (vM X) fun m =>
    bAnd(Nat.beq (Nat.land p m) (nat_lit 0),
      bAnd(Nat.blt p (Nat.shiftLeft (nat_lit 1) (nat_lit 84)),
        bAnd(Nat.blt m (Nat.shiftLeft (nat_lit 1) (nat_lit 84)),
          Nat.blt (nat_lit 0) (Nat.lor p m))))

@[expose] noncomputable def ordChk (KT O : Nat → Nat) (t : Nat) : Bool :=
  strictB (O t) fun o => strictB (key KT o) fun x =>
    bAnd(Nat.blt o (nat_lit 26572), bAnd(wf84 x,
      bIf(Nat.blt t (nat_lit 26571), Nat.blt (canonPk x) (canonPk (key KT (O (Nat.succ t)))),
        true)))

@[expose] noncomputable def ordChunk (KT O : Nat → Nat) (c : Nat) : Bool :=
  allN (nat_lit 2048) fun t =>
    (fun s => bIf(Nat.blt s (nat_lit 26572), ordChk KT O s, true))
      (Nat.add (Nat.mul (nat_lit 2048) c) t)

end CFSG.KC.D43

end
