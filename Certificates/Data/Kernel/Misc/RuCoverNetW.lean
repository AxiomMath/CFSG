module

public import Certificates.Data.Kernel.YModel.Model

public section

namespace CFSG.KC.Misc.RuCoverNet

open CFSG.KC CFSG.KC.YModel

@[expose] noncomputable def netCode (j s : Nat) : Nat := Nat.add (Nat.mul (nat_lit 2) (Nat.succ j)) s

@[expose] noncomputable def encZ (iA iB iZ : Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun n => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (netCode iZ (nat_lit 0)) (Nat.beq n (nat_lit 3)))
        (netCode iB (nat_lit 0)) (Nat.beq n (nat_lit 2)))
      (netCode iA (nat_lit 0)) (Nat.beq n (nat_lit 1)))
    (fun m => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (netCode iZ (nat_lit 1)) (Nat.beq m (nat_lit 2)))
        (netCode iB (nat_lit 1)) (Nat.beq m (nat_lit 1)))
      (netCode iA (nat_lit 1)) (Nat.beq m (nat_lit 0)))
    l

@[expose] noncomputable def packZ (iA iB iZ : Nat) (u : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l _ acc => Nat.lor (encZ iA iB iZ l) (Nat.shiftLeft acc (nat_lit 6))) u

@[expose] noncomputable def lenZ (u : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ n => Nat.succ n) u

@[expose] noncomputable def eqW (V : Nat → Nat) (iA iB iZ : Nat) (u v : List Int) : Bool :=
  sweqK (nat_lit 14) (nat_lit 6) V (packZ iA iB iZ u) (lenZ u) (packZ iA iB iZ v) (lenZ v)

@[expose] noncomputable def neW (V : Nat → Nat) (iA iB iZ : Nat) (u v : List Int) (b x y : Nat) :
    Bool :=
  andB (mapsTo (nat_lit 14) (nat_lit 6) V (packZ iA iB iZ u) (lenZ u) b x)
    (andB (mapsTo (nat_lit 14) (nat_lit 6) V (packZ iA iB iZ v) (lenZ v) b y)
      (notB (Nat.beq x y)))

end CFSG.KC.Misc.RuCoverNet

end
