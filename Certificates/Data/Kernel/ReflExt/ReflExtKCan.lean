module

public import Certificates.Data.Kernel.ReflExt.ReflExtK

public section

namespace CFSG.ReflExt.RXK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK

@[expose] noncomputable def lanes (D : Nat) (x : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih x => Nat.mod x 65536 :: ih (Nat.div x 65536)) D x

@[expose] noncomputable def canP (D : Nat) (a : Nat × Nat) : Bool :=
  Nat.beq (pk D (lanes D a.1)) a.1 && Nat.beq (pkr D (lanes D a.2).reverse) a.2

@[expose] noncomputable def canK (P : Pt) (d : FD) : Bool :=
  allK (fun rp => canP P.D rp.1 && allK (fun q => canP P.D q.1) rp.2.2.2.2.1) d.2.2.2.2

end CFSG.ReflExt.RXK

end
