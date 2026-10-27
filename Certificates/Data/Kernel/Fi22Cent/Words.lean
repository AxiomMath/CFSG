module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Fi22Cent

@[expose] noncomputable def wAt {α : Type} (f : α → Nat → Nat) (w : List α) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y) (fun l _ ih y => f l (ih y)) w y

end CFSG.KC.Fi22Cent

end
