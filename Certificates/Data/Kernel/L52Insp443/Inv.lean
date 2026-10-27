module

public import Certificates.Data.Kernel.L52Insp443.Sub
public import Certificates.Data.Kernel.L52Insp443.Tab

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM

@[expose] def letL {α β : Type} (a : α) (k : α → β) : β := k a

@[expose] noncomputable def invoK (c : Nat) : Bool :=
  CFSG.KC.Ord.andB (unitK c) (CFSG.KC.Ord.andB (Nat.beq (mmulK c c) idK) (CFSG.KC.Ord.notB (Nat.beq c idK)))

@[expose] noncomputable def ascK (lo : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih lo => CFSG.KC.Ord.andB (Nat.blt lo x) (ih x)) L lo

@[expose] noncomputable def lastK (lo : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun lo => lo) (fun x _ ih _ => ih x) L lo

@[expose] noncomputable def badK (ps qs : List Nat) (c : Nat) : Bool :=
  CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (mmulK (mmulK (List.getD ps 1 0) c) (List.getD qs 1 0)) c))
    (conjCommK c ps qs)

@[expose] noncomputable def orbIsK (O B : List Nat) : Bool :=
  CFSG.KC.Ord.andB (letL (spanK B) fun S => allK (fun o => memK o S) O)
    (letL (spanK O) fun S => allK (fun b => memK b S) B)

@[expose] noncomputable def orbOneK (ps qs : List Nat) (cs : List (List Nat)) (c : Nat) : Bool :=
  CFSG.KC.Ord.orB (CFSG.KC.Ord.notB (badK ps qs c)) (letL (orbK ps qs c) fun O => anyK (orbIsK O) cs)

end CFSG.KC.L52I

end
