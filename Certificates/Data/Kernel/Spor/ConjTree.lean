module

public import Certificates.Data.Kernel.Spor.RawTree

public section

namespace CFSG.KS.ConjTree

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def pconj (n w g x gi : Nat) : Nat :=
  pcomp n w (mask w) g (pcomp n w (mask w) x gi)

@[expose] noncomputable def stepSl (n w r : Nat) (GS GSI T : Nat → Nat) (TF wt N lo len : Nat) :
    Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i => bIf(Nat.blt i N,
    strictB (pg wt (mask wt) TF i) (fun t =>
      bAnd(Nat.blt (Nat.div t r) (Nat.succ i),
        Nat.beq (T (Nat.succ i)) (pconj n w (GS (Nat.mod t r)) (T (Nat.div t r))
          (GSI (Nat.mod t r))))), true)))

@[expose] noncomputable def ctEdgeB (r : Nat) (TF wt N j i j' : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) j', bAnd(Nat.ble j' N,
    Nat.beq (pg wt (mask wt) TF (Nat.pred j')) (Nat.add (Nat.mul j r) i)))

@[expose] noncomputable def actSl (n w r : Nat) (GS GSI T PA : Nat → Nat)
    (TF wt N wp m lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun j => bIf(Nat.blt j m,
    allN r (fun i => strictB (pg wp (mask wp) (PA i) j) (fun j' =>
      bAnd(Nat.blt j' m, bIf(ctEdgeB r TF wt N j i j', true,
        Nat.beq (pconj n w (GS i) (T j) (GSI i)) (T j'))))), true)))

@[expose] noncomputable def ctOrdSl (T : Nat → Nat) (ws SG RK m lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun j => bIf(Nat.blt j m,
    bAnd(strictB (pg ws (mask ws) RK j) (fun k =>
      bAnd(Nat.blt k m, Nat.beq (pg ws (mask ws) SG k) j)),
    bIf(Nat.blt (Nat.succ j) m,
      Nat.blt (T (pg ws (mask ws) SG j)) (T (pg ws (mask ws) SG (Nat.succ j))), true)), true)))

end CFSG.KS.ConjTree

end
