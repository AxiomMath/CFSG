module

public import Certificates.Data.Kernel.M1F2
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Co1B

open CFSG.KC.M1F2 (vmF strictB)
open CFSG.KC.Enum (pg)

@[expose] noncomputable def vAt (F : Nat → Nat) (a : Nat) : Nat :=
  pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) (F (Nat.div a (nat_lit 840))) (Nat.mod a (nat_lit 840))

@[expose] noncomputable def actPt (F : Nat → Nat) (TA TB v a b : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) v, bAnd(Nat.blt a (nat_lit 98280), bAnd(Nat.blt b (nat_lit 98280),
    bAnd(Nat.beq (vmF (nat_lit 24) TA v) (vAt F a), Nat.beq (vmF (nat_lit 24) TB v) (vAt F b)))))

@[expose] noncomputable def recAllB (f : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) Bool.true (fun t acc => bAnd(f t, acc)) n

@[expose] noncomputable def actFld (F : Nat → Nat) (TA TB P A B k : Nat) : Bool :=
  strictB (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k) (fun v =>
    strictB (pg (nat_lit 20) (CFSG.KS.mask (nat_lit 20)) A k) (fun a =>
      strictB (pg (nat_lit 20) (CFSG.KS.mask (nat_lit 20)) B k) (fun b => actPt F TA TB v a b)))

@[expose] noncomputable def actChunkK (F : Nat → Nat) (TA TB P A B : Nat) : Bool :=
  recAllB (actFld F TA TB P A B) (nat_lit 840)

end CFSG.KC.Co1B

end
