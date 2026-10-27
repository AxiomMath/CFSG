module

public import Certificates.Data.Kernel.SmithD6.WtCheck

public section

namespace CFSG.KD.SmithD6Adj

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def moveGo (x : Nat) (gs : List (List (Nat × Nat × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun ts _ ih => strictB (rhoT ts x) (fun r => bIf(Nat.beq r 0, ih, KT.memB r wt64Tree))) gs

@[expose] noncomputable def adjOK (x : Nat) : Bool :=
  strictB (rhoT (JT.gensT.getD 0 []) x)
    (fun r => bIf(Nat.beq r 0, moveGo x JT.gensT, KT.memB r wt64Tree))

@[expose] noncomputable def adjGo (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(adjOK x, ih)) l

@[expose] noncomputable def d6AdjOK (c : Nat) : Bool := adjGo (nthC J.wt64C c)

end CFSG.KD.SmithD6Adj

end
