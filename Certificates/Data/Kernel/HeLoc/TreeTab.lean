module

public import Certificates.Data.Kernel.HeLoc.Tree
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.HeLoc

open CFSG.KS.SporSch (eqOnL)
open CFSG.KC.LQT.P (allN)
open CFSG.KC.Enum (strictB)

@[expose] noncomputable def tabAtK (g rd : Nat → Nat → Nat) (T P Lb : Nat → Nat) (bs : List Nat)
    (i : Nat) : Bool :=
  strictB (T i) fun a => bIf(Nat.beq i 0, eqOnL bs (rd a) (fun b => b),
    strictB (T (P i)) fun c => strictB (Lb i) fun l => eqOnL bs (rd a) (fun b => g l (rd c b)))

@[expose] noncomputable def edgeTK (g rd : Nat → Nat → Nat) (T : Nat → Nat) (E : Nat → Nat → Nat)
    (N ng : Nat) (bs : List Nat) (i : Nat) : Bool :=
  strictB (T i) fun a => allN ng fun k => strictB (E i k) fun e =>
    bAnd(Nat.blt e N, strictB (T e) fun c => eqOnL bs (rd c) (fun b => g k (rd a b)))

end CFSG.KC.HeLoc

end
