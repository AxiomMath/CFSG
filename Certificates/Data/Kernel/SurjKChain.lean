module

public import Certificates.Data.Kernel.SurjK
public import Certificates.Data.Kernel.VecK

public section

namespace CFSG.KC.SurjChain

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

@[expose] noncomputable def wordRF (d : Nat) (F : Int → Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (idF d) (fun z _ ih => strictN ih fun x => mulF d x (F z)) w

@[expose] noncomputable def chainF (LM : List Nat) (z : Int) : Nat := getL (nat_lit 0) LM z.toNat

@[expose] noncomputable def partner (z : Int) : Int :=
  Int.ofNat (Nat.xor z.toNat (nat_lit 1))

@[expose] noncomputable def invWord (w : List Int) : List Int := (w.map partner).reverse

end CFSG.KC.SurjChain

end
