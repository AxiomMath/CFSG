module

public import Certificates.Data.Kernel.SmithD6.WtCheck
public import Certificates.Data.Kernel.SmithD6.T3cData

public section

namespace CFSG.KD.SmithD6

open CFSG.KC.KeyTree

@[expose] noncomputable def selGo (d : Nat) (bs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b _ ih k => Nat.xor (Nat.mul b (fld(d, k, 1))) (ih (Nat.succ k))) bs

@[expose] noncomputable def inFB (x : Nat) : Bool :=
  bAnd(Nat.blt 0 x, bAnd(Nat.blt x 4096, Nat.beq (Nat.land x 63) 0))

@[expose] noncomputable def selA (d : Nat) (B : Array Nat) : Bool :=
  Array.rec (motive := fun _ => Bool) (fun bs => inFB (selGo d bs 0)) B

@[expose] noncomputable def gramGo (ss : List Nat) : List (Array Nat) → List Nat → Bool :=
  List.rec (motive := fun _ => List (Array Nat) → List Nat → Bool) (fun _ _ => true)
    (fun s _ ih Bs ds => List.rec (motive := fun _ => Bool) false
      (fun B Bs' _ => List.rec (motive := fun _ => Bool) false
        (fun d ds' _ => bAnd(Bool.rec (motive := fun _ => Bool) (selA d B) true
          (Nat.beq (fld(s, 31, 1)) 1), ih Bs' ds')) ds) Bs) ss

@[expose] noncomputable def d6GramOK (c : Nat) : Bool :=
  gramGo (nthC J.wtC c) (nthA J.pbC c) (nthC JG.grC c)

end CFSG.KD.SmithD6

end
