module

public import Certificates.Data.Kernel.Co1Three.Slp

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2 CFSG.KC.Co1B

@[expose] noncomputable def cedgeK (TS E : Nat → Nat) (GN : List Nat) (c pc q : Nat) : Bool :=
  strictB (Nat.shiftRight q (nat_lit 1)) fun g =>
    bAnd(Nat.blt g (lenL GN),
      strictB (TS (getL (nat_lit 0) GN g)) fun X =>
        bIf(Nat.beq (Nat.land q (nat_lit 1)) (nat_lit 0),
          Nat.beq (mulWK X (E c)) (mulWK (E pc) X),
          Nat.beq (mulWK (E c) X) (mulWK X (E pc))))

@[expose] noncomputable def cforFromK (TS E : Nat → Nat) (GN : List Nat) (N : Nat) (RT : List Nat)
    (DP : Nat) : List Nat → Nat → Bool :=
  fun FT => List.rec (motive := fun _ => Nat → Bool) (fun c => Nat.beq c N)
    (fun e _ ih c => strictB c fun c => strictB (depK DP c) fun d =>
      bAnd(bIf(Nat.beq d (nat_lit 0), memK c RT,
        strictB (Nat.mod e N) fun pc =>
          bAnd(Nat.blt (nat_lit 0) pc, bAnd(Nat.beq (Nat.succ (depK DP pc)) d,
            cedgeK TS E GN c pc (Nat.div e N)))),
        ih (Nat.succ c))) FT

@[expose] noncomputable def cforK (TS E : Nat → Nat) (GN : List Nat) (N : Nat) (RT : List Nat)
    (DP : Nat) (FT : List Nat) : Bool :=
  cforFromK TS E GN N RT DP FT (nat_lit 1)

end CFSG.KC.Co1Cl

end
