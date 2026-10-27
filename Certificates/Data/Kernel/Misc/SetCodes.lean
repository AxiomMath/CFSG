module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.Misc.SetCodes

open CFSG.KC.Enum (pg)
open CFSG.KS (mask)
open CFSG.KC.LQT.P (allN anyN)

@[expose] noncomputable def maskK (L w s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pg w (mask w) s q))) L

@[expose] noncomputable def intoK (L w P s M : Nat) : Bool :=
  allN L fun q => Nat.testBit M (pg w (mask w) P (pg w (mask w) s q))

@[expose] noncomputable def permutesK (m L w : Nat) (SC : Nat → Nat) (P : Nat) : Bool :=
  allN m fun i => anyN m fun j => intoK L w P (SC i) (maskK L w (SC j))

@[expose] noncomputable def fixesK (m L w : Nat) (SC : Nat → Nat) (P : Nat) : Bool :=
  allN m fun i => intoK L w P (SC i) (maskK L w (SC i))

@[expose] noncomputable def actsK (m L w : Nat) (SC : Nat → Nat) (P : Nat) (σ : Nat → Nat) :
    Bool :=
  allN m fun i => intoK L w P (SC i) (maskK L w (SC (σ i)))

@[expose] noncomputable def setsK (n m L w : Nat) (SC : Nat → Nat) : Bool :=
  (allN m fun i => (allN L fun q => Nat.blt (pg w (mask w) (SC i) q) n) &&
      allN L fun q => allN q fun r =>
        !(Nat.beq (pg w (mask w) (SC i) q) (pg w (mask w) (SC i) r))) &&
    allN m fun i => allN m fun j => Nat.beq i j ||
      anyN L fun q => !(Nat.testBit (maskK L w (SC j)) (pg w (mask w) (SC i) q))

end CFSG.KC.Misc.SetCodes

end
