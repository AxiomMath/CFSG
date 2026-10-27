module

public import Init

public section

namespace CFSG.KC

@[expose] noncomputable def lnth {α : Type} (d : α) (l : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih j => Nat.rec (motive := fun _ => α) a (fun m _ => ih m) j) l

end CFSG.KC
