module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Pack

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def setO (q o mw v : Nat) : Nat :=
  Nat.add (Nat.sub q (Nat.shiftLeft fld(q, o, mw) o)) (Nat.shiftLeft v o)

@[expose] noncomputable def swapF (w m q a b : Nat) : Nat :=
  strictN (pg w m q a) (fun x => strictN (pg w m q b) (fun y =>
    strictN (setO q (Nat.mul w a) m y) (fun q' => setO q' (Nat.mul w b) m x)))

@[expose] noncomputable def swapsF (w m p T k : Nat) : Nat :=
  foldUp k (fun j q => swapF w m q (pg w m T (Nat.mul (nat_lit 2) j))
    (pg w m T (Nat.add (Nat.mul (nat_lit 2) j) (nat_lit 1)))) p

@[expose] noncomputable def signK (n w m p T k : Nat) : Bool :=
  bAnd(Nat.beq m (mask w),
    bAnd(allN k (fun j => strictB (pg w m T (Nat.mul (nat_lit 2) j)) (fun a =>
        strictB (pg w m T (Nat.add (Nat.mul (nat_lit 2) j) (nat_lit 1))) (fun b =>
          bAnd(Nat.blt a n, bAnd(Nat.blt b n, bIf(Nat.beq a b, false, true)))))),
      strictB (swapsF w m p T k) (fun q => allN n (fun i => Nat.beq (pg w m q i) i))))

end CFSG.KC.Pack

end
