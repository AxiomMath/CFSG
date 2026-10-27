module

public import Certificates.Data.Kernel.Co2Syl

public section

namespace CFSG.KC.Co2X9

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Syl

@[expose] noncomputable def orK (a b : Bool) : Bool := bIf(a, true, b)

@[expose] noncomputable def cenK (CF G : Nat → Nat) (D : Nat) (W : Nat → Nat) (k : Nat) : Bool :=
  letB (elemAt CF k) fun X => letB (mulV X X) fun S =>
    orK (Nat.beq S IDP) (orK (Nat.beq S D)
      (andK (Nat.blt (W k) (nat_lit 5)) (notK (commK (G (W k)) S))))

@[expose] noncomputable def blkX (CF G : Nat → Nat) (D : Nat) (W : Nat → Nat) (N b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andK (implK (Nat.blt (Nat.add (Nat.mul (nat_lit 64) b) i) N)
      (andK (recT CF G N (Nat.add (Nat.mul (nat_lit 64) b) i))
        (cenK CF G D W (Nat.add (Nat.mul (nat_lit 64) b) i)))) acc) (nat_lit 64)

@[expose] noncomputable def sqWK (CF : Nat → Nat) (N D k : Nat) : Bool :=
  andK (Nat.blt k N) (Nat.beq (mulV (elemAt CF k) (elemAt CF k)) D)

@[expose] noncomputable def conjK (F A B : Nat) : Bool := Nat.beq (mulV F A) (mulV B F)

@[expose] noncomputable def neK (D : Nat) : Bool := notK (Nat.beq D IDP)

end CFSG.KC.Co2X9

end
