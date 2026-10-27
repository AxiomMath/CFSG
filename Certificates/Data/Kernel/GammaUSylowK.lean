module

public import Certificates.Data.Kernel.IdxFourChainK

public section

namespace CFSG.KC.GUY

open CFSG.KC.IF4C

@[expose] noncomputable def minN (a b : Nat) : Nat := bif Nat.ble a b then a else b

@[expose] noncomputable def key4 (z z2 z3 : Nat) : Nat := minN z (minN z2 (minN z3 (mulP z z3)))

@[expose] noncomputable def key3 (z z2 : Nat) : Nat := key4 z z2 (mulP z z2)

@[expose] noncomputable def keyK (z : Nat) : Nat := key3 z (mulP z z)

@[expose] noncomputable def letG (SP SI l : Nat) : Nat :=
  bif Nat.blt l 2 then look SP l else look SI (l - 2)

@[expose] noncomputable def letV (SP SI l : Nat) : Nat :=
  bif Nat.blt l 2 then look SI l else look SP (l - 2)

@[expose] noncomputable def conjStep (SP SI Y ZP DP n x : Nat) (e : List Nat) : Bool :=
  bif Nat.beq (fld DP x) 0 then Nat.beq (look ZP x) (mulP Y idP)
  else Nat.blt (nthD 0 e 0) n && Nat.blt (fld DP (nthD 0 e 0)) (fld DP x) &&
    Nat.blt (nthD 0 e 1) 4 &&
    Nat.beq (look ZP x)
      (mulP (letG SP SI (nthD 0 e 1)) (mulP (look ZP (nthD 0 e 0)) (letV SP SI (nthD 0 e 1))))

@[expose] noncomputable def conjAt (SP SI Y ZP DP n x : Nat) (e : List Nat) (prev k : Nat)
    (rest : Nat → Nat → Bool) : Bool :=
  Nat.blt prev k && conjStep SP SI Y ZP DP n x e && rest (Nat.succ x) k

@[expose] noncomputable def conjRecs (SP SI Y ZP DP n : Nat) (es : List (List Nat)) (x prev : Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun e _ ih x prev => conjAt SP SI Y ZP DP n x e prev (keyK (look ZP x)) ih) es x prev

@[expose] noncomputable def conjOK (SP SI Y ZP DP n : Nat) (E : List (List Nat)) : Bool :=
  Nat.beq (lenN E) n && conjRecs SP SI Y ZP DP n E 0 0

@[expose] noncomputable def ordOK (Y : Nat) : Bool :=
  Nat.beq (mulP Y (mulP Y (mulP Y (mulP Y Y)))) idP && !Nat.beq (mulP Y idP) (mulP idP idP)

@[expose] noncomputable def ncP (a b : Nat) : Bool := !Nat.beq (mulP a b) (mulP b a)

@[expose] noncomputable def centOK (t : Nat) (gs : List Nat) : Bool :=
  gs.all fun g => Nat.beq (mulP g t) (mulP t g)
end CFSG.KC.GUY

end
