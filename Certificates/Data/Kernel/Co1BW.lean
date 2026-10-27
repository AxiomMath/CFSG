module

public import Certificates.Data.Kernel.Co1B
public import Certificates.Data.Kernel.F2Word

public section

namespace CFSG.KC.Co1B

open CFSG.KC.Loop CFSG.KC.Co1F2 CFSG.KC.F2W

@[expose] noncomputable def mulWK (A B : Nat) : Nat := mulW (nat_lit 24) A B

@[expose] noncomputable def wordABFrom (A B : Nat) (w : List Bool) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun b _ ih acc => strictN (mulWK acc (Bool.rec (motive := fun _ => Nat) B A b)) ih) w

@[expose] noncomputable def gwordFrom (G : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulWK acc (getL (nat_lit 0) G l)) ih) w

@[expose] noncomputable def powWK (M e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneK (fun _ acc => strictN acc fun a => mulWK a M) e

end CFSG.KC.Co1B

end
