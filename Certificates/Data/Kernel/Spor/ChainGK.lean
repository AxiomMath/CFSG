module

public import Certificates.Data.Kernel.Spor.ChainSK
public import Certificates.Data.Kernel.Spor.PChain

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS.CB CFSG.KS.PC

@[expose] noncomputable def siftG (n : Nat) (POS PAR LAB : Nat → Nat → Nat) (Mr B : Nat → Nat)
    (INV : Nat → Nat → Nat → Nat) (f i : Nat) (img : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool) (fun _ img => listEqK img (List.range n))
    (fun _ ih i img => strictB (POS i (List.getD img (B i) (nat_lit 0))) fun k =>
      bAnd(Nat.blt k (Mr i), ih (Nat.succ i) (mapK (trInvK (PAR i) (LAB i) (INV i) (Mr i) k) img)))
    f i img

@[expose] noncomputable def schG (n nb : Nat) (STEP INV : Nat → Nat → Nat → Nat)
    (PTS POS PAR LAB : Nat → Nat → Nat) (Mr B : Nat → Nat) (i h j : Nat) : Bool :=
  strictB (POS i (STEP i j (PTS i h))) fun k =>
    bAnd(Nat.blt k (Mr i), siftG n POS PAR LAB Mr B INV (Nat.sub nb (Nat.succ i)) (Nat.succ i)
      (List.map (schImg STEP INV PAR LAB Mr i h j k) (List.range n)))

@[expose] noncomputable def termG (n s nb : Nat) (F : Nat → Nat → Nat) (B : Nat → Nat) : Bool :=
  allN s fun j => bIf(fixesK F B nb j, allN n fun x => Nat.beq (F j x) x, true)

end CFSG.KS.CH

end
