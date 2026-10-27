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

@[expose] noncomputable def actSl (n w r : Nat) (GS GSI T PA : Nat → Nat) (wp m lo len : Nat) :
    Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun j => bIf(Nat.blt j m,
    allN r (fun i => strictB (pg wp (mask wp) (PA i) j) (fun j' =>
      bAnd(Nat.blt j' m, Nat.beq (pconj n w (GS i) (T j) (GSI i)) (T j')))), true)))

@[expose] noncomputable def distSl (T : Nat → Nat) (m lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun j => bIf(Nat.blt j m,
    strictB (T j) (fun x => allN j (fun k => Bool.not (Nat.beq x (T k)))), true)))

end CFSG.KS.ConjTree

end
