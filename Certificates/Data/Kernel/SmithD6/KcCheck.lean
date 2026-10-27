module

public import Certificates.Data.Kernel.SmithD6.WtCheck
public import Certificates.Data.Kernel.SmithD6.Trees
public import Certificates.Data.SmithD6RhoData

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree

@[expose] noncomputable def kcPick (x : Nat) : List Nat → List Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun b _ ih ps => List.rec (motive := fun _ => Nat) 0
      (fun p ps' _ => Nat.xor (Nat.mul b (fld(x, p, 1))) (ih ps')) ps)

@[expose] noncomputable def kcMem (bs ps : List Nat) (x : Nat) : Bool :=
  Nat.beq (kcPick x bs ps) x

@[expose] noncomputable def kcThrA (B P : Array Nat) : Nat :=
  Array.rec (motive := fun _ => Nat) (fun bs => Array.rec (motive := fun _ => Nat)
    (fun ps => nIf(kcMem bs ps 64, nIf(kcMem bs ps 128, 1, 0), 0)) P) B

@[expose] noncomputable def kcThrGo (Bs : List (Array Nat)) : List (Array Nat) → Nat :=
  List.rec (motive := fun _ => List (Array Nat) → Nat) (fun _ => 0)
    (fun B _ ih Ps => List.rec (motive := fun _ => Nat) 0
      (fun P Ps' _ => Nat.add (kcThrA B P) (ih Ps')) Ps) Bs

@[expose] noncomputable def kcThrC (Bss : List (List (Array Nat))) :
    List (List (Array Nat)) → Nat :=
  List.rec (motive := fun _ => List (List (Array Nat)) → Nat) (fun _ => 0)
    (fun Bs _ ih Pss => List.rec (motive := fun _ => Nat) 0
      (fun Ps Pss' _ => Nat.add (kcThrGo Bs Ps) (ih Pss')) Pss) Bss

@[expose] noncomputable def kcThrAll : Nat := kcThrC J.pbC J.ppC

@[expose] noncomputable def kcRk2Go : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun b _ ih a => bIf(Nat.beq (Nat.land b 63) 0, ih a,
      bIf(Nat.beq a 0, ih (Nat.land b 63), bIf(Nat.beq (Nat.land b 63) a, ih a, true))))

@[expose] noncomputable def kcRk2A (B : Array Nat) : Bool :=
  Array.rec (motive := fun _ => Bool) (fun bs => kcRk2Go bs 0) B

@[expose] noncomputable def kcMeetGo : List (Array Nat) → Bool → Bool :=
  List.rec (motive := fun _ => Bool → Bool) (fun _ => true)
    (fun B _ ih sk => bAnd(bIf(sk, true, kcRk2A B), ih false))

@[expose] noncomputable def d6KcMeetOK (c : Nat) : Bool := kcMeetGo (nthA J.pbC c) (Nat.beq c 0)

@[expose] noncomputable def kcSpanGo (t : KT) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun i _ ih m => bAnd(Nat.beq (KT.find (Nat.pow 2 m) t) (Nat.succ i), ih (Nat.succ m)))

@[expose] noncomputable def d6SpanOK : Bool := kcSpanGo wtTree spanIdx.toList 0

end CFSG.KD.SmithD6

end
