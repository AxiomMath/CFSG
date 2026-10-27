module

public import Certificates.Data.Kernel.BfsPinBase

public section

namespace CFSG.KC.PGrp

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def posWordK (n w : Nat) (G : Nat → Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (pcomp n w (mask w) acc (G l)) ih) wd (pidn n w)

@[expose] noncomputable def keyCK (n w : Nat) (ps : List Nat) (p q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ acc => Nat.add (pg w (mask w) p (pg w (mask w) q x)) (Nat.mul n acc)) ps

end CFSG.KC.PGrp

end
