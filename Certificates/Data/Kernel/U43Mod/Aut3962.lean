module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.U43Aut3962

open CFSG.KC.Enum

@[expose] noncomputable def mwv (w m X Y Xi Yi : Nat) (ws : List Nat) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun c _ ih q => strictN (ih q) (CFSG.KC.Enum.lt w m X Y Xi Yi c)) ws q

@[expose] noncomputable def mwvI (w m X Y Xi Yi : Nat) (ws : List Nat) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun c _ ih q => strictN (CFSG.KC.Enum.lt w m Xi Yi X Y c q) ih) ws q

@[expose] noncomputable def allIdx {α : Type} (f : α → Nat → Bool) (L : List α) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih k => bAnd(f x k, ih (Nat.succ k))) L k

@[expose] noncomputable def lSel {α : Type} (d : α) (L : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) L i

end CFSG.KC.U43Aut3962

end
